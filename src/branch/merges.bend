import Base
import ../resource/formats.bend as Formats
import ../resource/resources.bend as Resources
import ../shared/replica.bend as Replicas
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/rope.bend as Ropes
import ../shared/shared/shared/depot.bend as Depots
import ../shared/shared/shared/pack.bend as Packs
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/side.bend as Sides
import ../shared/shared/shared/text.bend as Texts
import ../shared/shared/tree.bend as Trees
import ../shared/vend.bend as Vend
import ../writer/requests.bend as Requests

# Trees being written
# -------------------

# a tree being written: the ledger with its new nodes, its root, and the new
# nodes
type Work<-L: Data> is Data:
  Work{ledger: L, root: Maybe<&2, Hashes.Hash>, nodes: List<&2, List<&2, U32>>}

# the work on l with the nodes ns, after the tree p
def Work.put(
  ~d: Vend.Led(),
  l: Vend.L(d),
  ns: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Maybe<&2, Work<Vend.L(d)>>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Work{
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(x), l),
          Trees.Edit.root(x),
          List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(x))
        }
      }

# the work w with the key k set to the value m (none: deleted; none at all:
# the ledger lacks a node)
def Work.set(~d: Vend.Led(), w: Work<Vend.L(d)>, k: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Work<Vend.L(d)>>:
  match w:
    case Work{+l, h, ns}:
      Work.put(~d, l, ns, Replicas.Tree.put(~Requests.Ask.machine(), ~d, l, h, k, m))

# the work w with the nodes ms as data
def Work.keep(~d: Vend.Led(), w: Work<Vend.L(d)>, +ms: List<&2, List<&2, U32>>) -> Work<Vend.L(d)>:
  match w:
    case Work{l, h, ns}:
      Work{
        Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, l),
        h,
        List.append(&2, List<&2, U32>, ns, ms)
      }

# the work w with the resource n among the open clashes of the merge k
def Work.clash(~d: Vend.Led(), w: Work<Vend.L(d)>, +k: Ledgers.Id, n: Resources.Name) -> Maybe<&2, Work<Vend.L(d)>>:
  match w:
    case Work{+l, +h, ns}:
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Work<Vend.L(d)>,
        Vend.Clash.names(~d, l, h, k),
        cs => Work.set(~d, Work{l, h, ns}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
      )

# the act that takes the work m as the content, with the owners vs if any,
# once each node that the work adds reads back from its ledger: a node whose
# hash another one holds waits, so what an act writes is what a read finds
def Work.act(~d: Vend.Led(), vs: Maybe<&2, List<&2, String>>, m: Maybe<&2, Work<Vend.L(d)>>) -> Maybe<&2, Replicas.Act>:
  match m:
    case None{}:
      None{}
    case Some{Work{l, h, +ns}}:
      Shared.Maybe.when(
        Replicas.Act,
        Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, ns),
        u => Some{Replicas.Act.Taken{vs, h, ns}}
      )

# what a resolve of the resource n of the merge k, with the content x, does
# at the tip t: while the clash is open, and once l holds the bytes, the
# resource holds x and the clash is shut; else it is stale (none: wait for
# what l lacks)
def Resolve.act.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    List<&2, Resources.Name>,
    Replicas.Act,
    Vend.Clash.names(~d, l, Replicas.Tip.content(t), k),
    +cs => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, l, new),
        v => Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Work<Vend.L(d)>,
            Work<Vend.L(d)>,
            Work.set(~d, Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Work.set(
              ~d,
              w,
              Vend.Key.clashes(k),
              Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))
            )
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}}
    )
  )

# what a resolve does (Resolve.act.of), once the root of its content is known
def Resolve.act(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  k: Ledgers.Id,
  +n: Resources.Name,
  x: Requests.Content
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Vend.Content.find(~d, l, t, n, x),
    new => Resolve.act.of(~d, l, t, k, n, new)
  )

# Merges
# ------
# A merge goes resource by resource, each in its own format. It takes theirs
# and the base as trees that come with the change.

# what a merge keeps of a resource: one side (none: removed), new bytes in a
# format, or a clash
type Pick is Data:
  Pick.Take{res: Maybe<&2, Requests.Res>}
  Pick.Make{format: Hashes.Hash, bytes: Texts.Bytes()}
  Pick.Clash{}

# the pick of a merge of bytes in the format whose hash is h
def Pick.of(h: Hashes.Hash, m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Pick.Make{h, x}
    case Formats.Merged.Clash{}:
      Pick.Clash{}

# what a submodule holds: a version of a branch of another store, by its
# number on the branch and its request. The history of a branch is one line,
# so of two pointers to one branch the higher number is the newer
type Pointer is Data:
  Pointer{store: Hashes.Hash, branch: String, number: U32, version: Ledgers.Id}

# the pointer x, then r
def Pointer.code(x: Pointer, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Pointer{st, b, k, v}:
      Hashes.Hash.code(st, Codes.Code.text(b, k <> Ledgers.Id.code(v, r)))

# a pointer
def Pointer.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Pointer>>:
  Codes.Code.four.read(
    ~Hashes.Hash,
    ~String,
    ~U32,
    ~Ledgers.Id,
    ~Pointer,
    ~Hashes.Hash.code.read,
    ~Codes.Code.text.read,
    ~Codes.Code.token.read,
    ~Ledgers.Id.code.read,
    st => b => k => v => Pointer{st, b, k, v},
    ts
  )

# a pointer reads back from its code: a submodule names one version of one
# branch of one store
law Pointer.code_read:
  for x: Pointer
  for r: List<&2, U32>
  {Pointer.code.read(Pointer.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Pointer>>}

def Pointer.code_read(x, r):
  match x:
    case Pointer{st, b, k, v}:
      Codes.Code.four_read(
        ~Hashes.Hash,
        ~String,
        ~U32,
        ~Ledgers.Id,
        ~Pointer,
        ~Hashes.Hash.codec(),
        ~Codes.Code.text.codec(),
        ~Codes.Code.token.codec(),
        ~Ledgers.Id.codec(),
        w => y => z => q => Pointer{w, y, z, q},
        st,
        b,
        k,
        v,
        r
      )

# the bytes of a submodule that holds the pointer x: its code, four bytes in a
# word
def Pointer.bytes(x: Pointer) -> Texts.Bytes():
  Packs.Pack.unpack(Pointer.code(x, []))

# the pointer that the bytes b of a submodule hold
def Pointer.read(b: Texts.Bytes()) -> Maybe<&2, Pointer>:
  Codes.Code.whole.read(~Pointer, ~Pointer.code, ~Pointer.code.read, Packs.Pack.words(b))

# the newer of the pointers x and y, when they point to one branch of one
# store and their numbers differ, or they are the same
def Pointer.newer(x: Pointer, y: Pointer) -> Maybe<&2, Pointer>:
  match x y:
    case Pointer{+s1, +b1, +k1, +v1} Pointer{+s2, +b2, +k2, +v2}:
      Shared.Bool.when(
        Maybe<&2, Pointer>,
        List.all.if(u => String.eq(b1, b2), Hashes.Hash.is_eq(s1, s2)),
        u => Shared.Bool.when(
          Maybe<&2, Pointer>,
          U32.is_lt(k1, k2),
          v => Some{Pointer{s2, b2, k2, v2}},
          v => Shared.Bool.when(
            Maybe<&2, Pointer>,
            U32.is_lt(k2, k1),
            w => Some{Pointer{s1, b1, k1, v1}},
            w => Shared.Maybe.when(
              Pointer,
              Ledgers.Id.is_eq(v1, v2),
              z => Some{Pointer{s1, b1, k1, v1}}
            )
          )
        ),
        u => None{}
      )

# the merge of two submodules that hold the pointers x and y, in the format
# whose hash is h: the newer one; a clash when they point to two branches, or
# a pointer does not read
def Pointer.merge(h: Hashes.Hash, x: Maybe<&2, Pointer>, y: Maybe<&2, Pointer>) -> Pick:
  match x y:
    case Some{px} Some{py}:
      Maybe.default(
        &2,
        Pick,
        Maybe.bind(&2, Pointer, Pick, Pointer.newer(px, py), p => Some{Pick.Make{h, Pointer.bytes(p)}}),
        Pick.Clash{}
      )
    case a b:
      Pick.Clash{}

# the bytes of the resource m: a resource that is not there is empty
def Res.text(~d: Vend.Led(), l: Vend.L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case None{}:
      Some{[]}
    case Some{x}:
      Vend.Root.bytes(~d, l, Vend.Res.root(x))

# the hash of the format of the resource m, else of n: the format of a merge
def Res.format.of(m: Maybe<&2, Requests.Res>, n: Maybe<&2, Requests.Res>) -> Maybe<&2, Hashes.Hash>:
  match m n:
    case Some{x} y:
      Some{Vend.Res.format.hash(x)}
    case None{} Some{y}:
      Some{Vend.Res.format.hash(y)}
    case None{} None{}:
      None{}

# the two sides hold one format, or one side holds none
def Res.one_format(+o: Maybe<&2, Requests.Res>, +t: Maybe<&2, Requests.Res>) -> Bool:
  match o t:
    case Some{x} Some{y}:
      Hashes.Hash.is_eq(Vend.Res.format.hash(x), Vend.Res.format.hash(y))
    case a b:
      True{}

# Pick.in once the bytes ob of ours and tb of theirs are known
def Pick.format(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  h: Hashes.Hash,
  f: Formats.Format,
  b: Maybe<&2, Requests.Res>,
  ob: Texts.Bytes(),
  tb: Texts.Bytes()
) -> Maybe<&2, Pick>:
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      Some{Pointer.merge(h, Pointer.read(ob), Pointer.read(tb))}
    case g:
      Maybe.bind(
        &2,
        Texts.Bytes(),
        Pick,
        Res.text(~d, l, b),
        bb => Some{Pick.of(h, Formats.Format.merge(g, bb, ob, tb))}
      )

# the pick of a merge of both changes in the format f, whose hash is h: a
# submodule takes the newer pointer, any other format merges its bytes (none:
# wait for bytes)
def Pick.in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Hashes.Hash,
  f: Formats.Format,
  b: Maybe<&2, Requests.Res>,
  o: Maybe<&2, Requests.Res>,
  t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Maybe.bind(
    &2,
    Texts.Bytes(),
    Pick,
    Res.text(~d, l, o),
    ob => Maybe.bind(
      &2,
      Texts.Bytes(),
      Pick,
      Res.text(~d, l, t),
      tb => Pick.format(~d, l, h, f, b, ob, tb)
    )
  )

# the pick of a merge of both changes (none: wait for a format or bytes). Two
# sides in two formats clash
def Pick.both(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Shared.Bool.when(
    Maybe<&2, Pick>,
    Res.one_format(o, t),
    u => Maybe.default(
      &2,
      Maybe<&2, Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Pick>,
        Res.format.of(o, t),
        +h => Some{
          Maybe.bind(
            &2,
            Formats.Format,
            Pick,
            Vend.Format.at(~d, l, h),
            f => Pick.in(~d, l, h, f, b, o, t)
          )
        }
      ),
      Some{Pick.Take{None{}}}
    ),
    u => Some{Pick.Clash{}}
  )

# what a merge keeps of a resource, once the side s is known
def Pick.side(
  ~d: Vend.Led(),
  l: Vend.L(d),
  b: Maybe<&2, Requests.Res>,
  o: Maybe<&2, Requests.Res>,
  t: Maybe<&2, Requests.Res>,
  s: Sides.Side
) -> Maybe<&2, Pick>:
  match s:
    case Sides.Side.Theirs{}:
      Some{Pick.Take{t}}
    case Sides.Side.Ours{}:
      Some{Pick.Take{o}}
    case Sides.Side.Both{}:
      Pick.both(~d, l, b, o, t)

# what a merge of the base b, ours o and theirs t keeps of a resource: the
# side that Side.of takes (theirs when ours is the base; ours when theirs is
# the base or both agree), else both merged, in their format. So a merge never
# loses a change that only one side made (Sides.Side.keeps_changes)
def Pick.merge(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Pick.side(~d, l, b, o, t, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, t))

# the work w with the resource n as the pick p says, for the merge k: a clash
# keeps ours and opens the clash of the resource
def Merge.pick(
  ~d: Vend.Led(),
  w: Work<Vend.L(d)>,
  k: Ledgers.Id,
  +n: Resources.Name,
  p: Pick
) -> Maybe<&2, Work<Vend.L(d)>>:
  match p:
    case Pick.Take{x}:
      Work.set(~d, w, Vend.Key.res(n), Vend.Res.value(x))
    case Pick.Make{h, bytes}:
      +r = Ropes.Rope.of_bytes(bytes)
      Work.set(
        ~d,
        Work.keep(~d, w, Ropes.Put.nodes(r)),
        Vend.Key.res(n),
        Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(r)}})
      )
    case Pick.Clash{}:
      Work.clash(~d, w, k, n)

# the name of the resource of the key k, when it is the key of one
def Res.name(k: List<&2, U32>) -> Maybe<&2, Resources.Name>:
  match k:
    case Con{0, r}:
      Codes.Code.whole.read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, r)
    case _:
      None{}

# the work m after the merge of the resource n: the pick of the base hb, ours
# ho and theirs ht, read in l (none: wait for a node or for bytes)
def Merge.one(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +w: Work<Vend.L(d)>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<Vend.L(d)>,
    Vend.Res.find(~d, l, hb, n),
    +b => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Work<Vend.L(d)>,
      Vend.Res.find(~d, l, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Work<Vend.L(d)>,
        Vend.Res.find(~d, l, ht, n),
        t => Maybe.bind(
          &2,
          Pick,
          Work<Vend.L(d)>,
          Pick.merge(~d, l, b, o, t),
          p => Merge.pick(~d, w, k, n, p)
        )
      )
    )
  )

# the work m after the merge of each resource among the keys xs. A
# resource that comes twice is merged twice, with the same pick
def Merge.all(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  m: Maybe<&2, Work<Vend.L(d)>>
) -> Maybe<&2, Work<Vend.L(d)>>:
  match xs m:
    case Nil{} y:
      y
    case Con{x, rest} None{}:
      None{}
    case Con{x, rest} Some{+w}:
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        rest,
        Maybe.default(
          &2,
          Maybe<&2, Work<Vend.L(d)>>,
          Maybe.bind(
            &2,
            Resources.Name,
            Maybe<&2, Work<Vend.L(d)>>,
            Res.name(x),
            n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
          ),
          Some{w}
        )
      )

# the root of the tree of the base m of a merge: no base is the empty tree
def Base.tree(m: Maybe<&2, Requests.Source>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Vend.Source.root(s)

# what the merge k of the source from, since the base, does at the tip t:
# once l holds the three whole trees, each resource that ours and theirs hold
# differently gets its pick (Pick.merge); every other resource stays
def Merge.act(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  t: Replicas.Tip,
  +k: Ledgers.Id,
  from: Requests.Source,
  base: Maybe<&2, Requests.Source>
) -> Maybe<&2, Replicas.Act>:
  +ho = Replicas.Tip.content(t)
  +ht = Vend.Source.root(from)
  +hb = Base.tree(base)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    List.all.if(u => List.all.if(u2 => Vend.Tree.kept(~d, l, ho), Vend.Tree.kept(~d, l, hb)), Vend.Tree.kept(~d, l, ht)),
    u => Work.act(
      ~d,
      None{},
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
          []
        ),
        Some{Work{l, ho, []}}
      )
    ),
    u => None{}
  )

# Merging, one tree at a time
# ---------------------------
# Lemmas for the two laws below. They read the ledger d only by its laws: a
# write changes its key and no other, and what a taken act writes reads back.

# both A and B, as Data: a proof of it may be used as often as a proof needs
def Merge.And(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# the nodes ns2 are the nodes ns, then others
def Merge.Nodes(-ns: List<&2, List<&2, U32>>, -ns2: List<&2, List<&2, U32>>) -> Data:
  Sigma<&2, &2, List<&2, List<&2, U32>>, ex => {ns2 == List.append(&2, List<&2, U32>, ns, ex): List<&2, List<&2, U32>>}>

# the add law of the laws of a ledger
def Merge.get_add.of(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  laws: Ledgers.Ledger.Laws(Q, c, k)
) -> Ledgers.Laws.GetAdd(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, rest}}:
      ga

# a ledger with one more entry holds what it held, and the entry when its name
# was free
def Merge.get_add(~d: Vend.Led()) -> Ledgers.Laws.GetAdd(
  Requests.Ask,
  Replicas.Machine.code(Requests.Ask.machine()),
  Replicas.Led.kind(Requests.Ask.machine(), d)
):
  Merge.get_add.of(
    Requests.Ask,
    Replicas.Machine.code(Requests.Ask.machine()),
    Replicas.Led.kind(Requests.Ask.machine(), d),
    Replicas.Led.laws(Requests.Ask.machine(), d)
  )

# the entry e, when it is under the name n
def Merge.new_entry(~d: Vend.Led(), +e: Ledgers.Entry<Requests.Ask>, n: Ledgers.Name) -> Maybe<&2, Ledgers.Entry<Requests.Ask>>:
  Shared.Maybe.when(
    Ledgers.Entry<Requests.Ask>,
    Ledgers.Name.is_eq(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e), n),
    u => Some{e}
  )

# what a read finds first, it finds before what comes after
def Merge.or_keeps(
  -A: Data,
  a: Maybe<&2, A>,
  b: Maybe<&2, A>,
  x: A,
  e: {a == Some{x}: Maybe<&2, A>}
) -> {Maybe.or(&2, A, a, b) == Some{x}: Maybe<&2, A>}:
  %Equal.sym(Maybe<&2, A>, a, Some{x}, e): {Maybe.or(&2, A, _, b) == Some{x}: Maybe<&2, A>}
  {==}

# a ledger that gets some data, then some more, is a ledger that gets both
def Merge.puts_append(
  ~d: Vend.Led(),
  as: List<&2, List<&2, U32>>,
  +bs: List<&2, List<&2, U32>>,
  +l: Vend.L(d)
) -> {
  Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, as, bs), l)
    == Replicas.Led.puts(~Requests.Ask.machine(), ~d, bs, Replicas.Led.puts(~Requests.Ask.machine(), ~d, as, l)): Vend.L(d)
}:
  match as:
    case Nil{}:
      {==}
    case Con{+ws, rest}:
      Merge.puts_append(~d, rest, bs, Replicas.Led.add(~Requests.Ask.machine(), ~d, l, Ledgers.Entry.Data{ws}))

# Merge.holds_fetch for the first words x of the list, once the checks are known
def Merge.holds_fetch.cons(
  ~d: Vend.Led(),
  +s: Vend.L(d),
  +x: List<&2, U32>,
  rest: List<&2, List<&2, U32>>,
  +w: List<&2, U32>,
  +q: Bool,
  +p: Bool,
  hq: {
    Depots.Depot.has(~Vend.L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, x) == q: Bool
  },
  hp: {Shared.List.is_eq(~U32, ~U32.is_eq, x, w) == p: Bool},
  h: {
    List.all.if(
      u => Depots.Depot.holds(~Vend.L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, rest),
      q
    )
      == True{}: Bool
  },
  c: {
    List.any.if(
      u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, w),
      p
    )
      == True{}: Bool
  },
  ih: {
    Depots.Depot.holds(~Vend.L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, rest) == True{}: Bool
  } -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, w) == True{}: Bool
  } -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match q p:
    case True{} True{}:
      %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, w)(hp): {
        Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(_)) == Some{_}: Maybe<&2, List<&2, U32>>
      }
      Replicas.Hist.has(~Requests.Ask.machine(), ~d, s, x)(hq)
    case True{} False{}:
      ih(h)(c)
    case False{} y:
      Empty.absurd(
        {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(h)
      )

# a depot that holds each of some words gives each of them under its hash
def Merge.holds_fetch(
  ~d: Vend.Led(),
  +s: Vend.L(d),
  ns: List<&2, List<&2, U32>>,
  +w: List<&2, U32>
) -> {
  Depots.Depot.holds(~Vend.L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, ns) == True{}: Bool
} -> {
  List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ns, w) == True{}: Bool
} -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match ns:
    case Nil{}:
      h => c => Empty.absurd(
        {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(c)
      )
    case Con{+x, +rest}:
      h => c => Merge.holds_fetch.cons(
        ~d,
        s,
        x,
        rest,
        w,
        Depots.Depot.has(~Vend.L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, x),
        Shared.List.is_eq(~U32, ~U32.is_eq, x, w),
        {==},
        {==},
        h,
        c,
        Merge.holds_fetch(~d, s, rest, w)
      )

# the ledger of the work w
def Merge.ledger(~d: Vend.Led(), w: Work<Vend.L(d)>) -> Vend.L(d):
  match w:
    case Work{l, h, ns}:
      l

# the tree of the work w
def Merge.root(~d: Vend.Led(), w: Work<Vend.L(d)>) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{l, h, ns}:
      h

# the nodes that the work w added
def Merge.nodes(~d: Vend.Led(), w: Work<Vend.L(d)>) -> List<&2, List<&2, U32>>:
  match w:
    case Work{l, h, ns}:
      ns

# no nodes are no more nodes
def Merge.nodes_refl(+ns: List<&2, List<&2, U32>>) -> Merge.Nodes(ns, ns):
  (
    [],
    Equal.sym(
      List<&2, List<&2, U32>>,
      List.append(&2, List<&2, U32>, ns, []),
      ns,
      Shared.List.append_nil(List<&2, U32>, ns)
    )
  )

# the nodes after the nodes after a are the nodes after a
def Merge.nodes_trans(
  +a: List<&2, List<&2, U32>>,
  +b: List<&2, List<&2, U32>>,
  +c: List<&2, List<&2, U32>>,
  x: Merge.Nodes(a, b),
  y: Merge.Nodes(b, c)
) -> Merge.Nodes(a, c):
  (+ex1, p1) = x
  (+ex2, p2) = y
  (
    List.append(&2, List<&2, U32>, ex1, ex2),
    %Shared.List.append_assoc(List<&2, U32>, a, ex1, ex2): {c == _: List<&2, List<&2, U32>>}
    %p1: {c == List.append(&2, List<&2, U32>, _, ex2): List<&2, List<&2, U32>>}
    p2
  )

# the nodes after a and the nodes ne are nodes after a
def Merge.nodes_drop(
  +a: List<&2, List<&2, U32>>,
  +ne: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(List.append(&2, List<&2, U32>, a, ne), N)
) -> Merge.Nodes(a, N):
  (+ex, pe) = nd
  (
    List.append(&2, List<&2, U32>, ne, ex),
    %Shared.List.append_assoc(List<&2, U32>, a, ne, ex): {N == _: List<&2, List<&2, U32>>}
    pe
  )

# the nodes after a are those after b, when a is b
def Merge.nodes_cast(
  +a: List<&2, List<&2, U32>>,
  +a2: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  e: {a == a2: List<&2, List<&2, U32>>},
  nd: Merge.Nodes(a, N)
) -> Merge.Nodes(a2, N):
  %e: Merge.Nodes(_, N)
  nd

# a node among those that come after a and the nodes ne is among those that
# come after
def Merge.nodes_contains(
  +a: List<&2, List<&2, U32>>,
  +ne: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(List.append(&2, List<&2, U32>, a, ne), N),
  +w: List<&2, U32>,
  c: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ne, w) == True{}: Bool}
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), N, w) == True{}: Bool}:
  (+ex, pe) = nd
  %Equal.sym(
    List<&2, List<&2, U32>>,
    N,
    List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, a, ne), ex),
    pe
  ): {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), _, w) == True{}: Bool}
  Shared.List.contains_left(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    List.append(&2, List<&2, U32>, a, ne),
    ex,
    w,
    Shared.List.contains_right(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), a, ne, w, c)
  )

# a ledger that gets the nodes ns, from the one that gets the nodes ps, grows
# from it
def Merge.grows_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +lf: Vend.L(d),
  +ps: List<&2, List<&2, U32>>,
  +ns: List<&2, List<&2, U32>>,
  wc: {lc == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l): Vend.L(d)},
  wf: {lf == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l): Vend.L(d)},
  nd: Merge.Nodes(ps, ns)
) -> Replicas.Led.Grows(Requests.Ask.machine(), d, lc, lf):
  (+ex, pe) = nd
  %Equal.sym(Vend.L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l), wc): Replicas.Led.Grows(Requests.Ask.machine(), d, _, lf)
  %Equal.sym(Vend.L(d), lf, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), wf): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    _
  )
  %Equal.sym(List<&2, List<&2, U32>>, ns, List.append(&2, List<&2, U32>, ps, ex), pe): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l)
  )
  %Equal.sym(
    Vend.L(d),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, ps, ex), l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ex, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l)),
    Merge.puts_append(~d, ps, ex, l)
  ): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    _
  )
  Replicas.Hist.puts(~Requests.Ask.machine(), ~d, ex, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l))

# what a write of the key kw to the value m, to the tree hc, gives in the ledger
# lf: the new tree h1 reads the key as written, and each other key as hc did
def Merge.Writes(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Type:
  {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, kw) == Trees.Look.of(m): Trees.Look}
    & (
      @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> {Shared.List.is_eq(~U32, ~U32.is_eq, kw, k2) == False{}: Bool} -> {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    )

# the data of the ledger lf that holds the nodes N are the nodes N
def Merge.Held(~d: Vend.Led(), lf: Vend.L(d), N: List<&2, List<&2, U32>>) -> Data:
  {
    Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lf, N) == True{}: Bool
  }

# the ledger lc is the ledger l with the nodes ps
def Merge.Puts(~d: Vend.Led(), l: Vend.L(d), lc: Vend.L(d), ps: List<&2, List<&2, U32>>) -> Data:
  {lc == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l): Vend.L(d)}

# the work after a write of the edit e is the work of its ledger, tree and nodes
def Merge.put_work(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<Vend.L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> {
  Work{
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
    Trees.Edit.root(e),
    List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
  }
    == W1: Work<Vend.L(d)>
}:
  Shared.Maybe.some_inj(
    Work<Vend.L(d)>,
    Work{
      Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
      Trees.Edit.root(e),
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
    },
    W1,
    e1
  )

# the tree of the work after a write of the edit e is the tree of e
def Merge.put_root(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<Vend.L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> {Trees.Edit.root(e) == Merge.root(~d, W1): Maybe<&2, Hashes.Hash>}:
  Equal.cong(
    Work<Vend.L(d)>,
    Maybe<&2, Hashes.Hash>,
    w => Merge.root(~d, w),
    Work{
      Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
      Trees.Edit.root(e),
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
    },
    W1,
    Merge.put_work(~d, lc, P, e, W1, e1)
  )

# the nodes of the work after a write of the edit e are those before it, and
# the nodes of e
def Merge.put_nodes(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<Vend.L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Nodes(List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), N):
  Merge.nodes_cast(
    Merge.nodes(~d, W1),
    List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)),
    N,
    Equal.sym(
      List<&2, List<&2, U32>>,
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)),
      Merge.nodes(~d, W1),
      Equal.cong(
        Work<Vend.L(d)>,
        List<&2, List<&2, U32>>,
        w => Merge.nodes(~d, w),
        Work{
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
          Trees.Edit.root(e),
          List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
        },
        W1,
        Merge.put_work(~d, lc, P, e, W1, e1)
      )
    ),
    nd
  )

# the work W1 is the work after a write of the key kw to the value m, to the
# tree hc of the work with the ledger lc and the nodes P, when the ledger lf
# holds the nodes N that come after those of W1
def Merge.set_core(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +kw: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  p: Maybe<&2, Trees.Edit>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, kw, m) == p: Maybe<&2, Trees.Edit>},
  +e1: {Work.put(~d, lc, P, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Writes(~d, lf, Merge.root(~d, W1), hc, kw, m):
  match p:
    case None{}:
      Empty.absurd(Merge.Writes(~d, lf, Merge.root(~d, W1), hc, kw, m), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e1))
    case Some{+e}:
      %Merge.put_root(~d, lc, P, e, W1, e1): Merge.Writes(~d, lf, _, hc, kw, m)
      Replicas.Hist.write(Requests.Ask.machine(), d)(lc)(lf)(hc)(kw)(m)(e)(ep)(
        Merge.grows_of(~d, l, lc, lf, P, N, wc, wf, Merge.nodes_drop(P, Trees.Edit.nodes(e), N, Merge.put_nodes(~d, lc, P, e, W1, e1, N, nd)))
      )(+w => c => Merge.holds_fetch(~d, lf, N, w)(held)(Merge.nodes_contains(P, Trees.Edit.nodes(e), N, Merge.put_nodes(~d, lc, P, e, W1, e1, N, nd), w, c)))

# the work after a write has the ledger of the nodes that it has, and its nodes
# come after those before it
def Merge.set_facts.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  p: Maybe<&2, Trees.Edit>,
  +e1: {Work.put(~d, lc, P, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match p:
    case None{}:
      Empty.absurd(
        Merge.And(
          Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
          Merge.Nodes(P, Merge.nodes(~d, W1))
        ),
        Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e1)
      )
    case Some{+e}:
      %Merge.put_work(~d, lc, P, e, W1, e1): Merge.And(
        Merge.Puts(~d, l, Merge.ledger(~d, _), Merge.nodes(~d, _)),
        Merge.Nodes(P, Merge.nodes(~d, _))
      )
      (
        %Equal.sym(Vend.L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l), wc): {
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), _)
            == Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), l): Vend.L(d)
        }
        Equal.sym(
          Vend.L(d),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), l),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l)),
          Merge.puts_append(~d, P, Trees.Edit.nodes(e), l)
        ),
        (Trees.Edit.nodes(e), {==})
      )

# the work after a write of the key kw to the value m has the ledger of the
# nodes that it has, and its nodes come after those before it
def Merge.set_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +kw: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +e1: {Work.set(~d, Work{lc, hc, P}, kw, m) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  Merge.set_facts.at(
    ~d,
    l,
    lc,
    P,
    W1,
    Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, kw, m),
    e1,
    wc
  )

# the key written is the key read, when the write is read
def Merge.writes_hit(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m)
) -> {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, kw) == Trees.Look.of(m): Trees.Look}:
  match wr:
    case Tuple{hit, frame}:
      hit

# a key other than the key written is read as before, when the write is read
def Merge.writes_frame(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  k2: List<&2, U32>,
  x: Maybe<&2, List<&2, U32>>,
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, k2) == False{}: Bool},
  kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match wr:
    case Tuple{hit, frame}:
      frame(k2)(x)(hk)(kn)

# the ledger of a work that gets more nodes is the ledger of the nodes that it
# has
def Merge.keep_puts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +ms: List<&2, List<&2, U32>>,
  wc: Merge.Puts(~d, l, lc, P)
) -> Merge.Puts(
  ~d,
  l,
  Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, lc),
  List.append(&2, List<&2, U32>, P, ms)
):
  %Equal.sym(Vend.L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l), wc): {
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, _)
      == Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, ms), l): Vend.L(d)
  }
  Equal.sym(
    Vend.L(d),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, ms), l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l)),
    Merge.puts_append(~d, P, ms, l)
  )

# the facts about the work after a pick that makes nodes, from those of the
# write that follows them
def Merge.pick_facts.make(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +ms: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  f: Merge.And(
    Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
    Merge.Nodes(List.append(&2, List<&2, U32>, P, ms), Merge.nodes(~d, W1))
  )
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  (+a, nd) = f
  (
    a,
    Merge.nodes_trans(P, List.append(&2, List<&2, U32>, P, ms), Merge.nodes(~d, W1), (ms, {==}), nd)
  )

# the facts about the work after a clash, once the clashes that are open are
# read (mc)
def Merge.pick_facts.clash.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<Vend.L(d)>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<Vend.L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<Vend.L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match mc:
    case None{}:
      Empty.absurd(
        Merge.And(
          Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
          Merge.Nodes(P, Merge.nodes(~d, W1))
        ),
        Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, eb)
      )
    case Some{+cs}:
      Merge.set_facts(~d, l, lc, hc, P, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)), W1, eb, wc)

# the facts about the work after a clash
def Merge.pick_facts.clash(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<Vend.L(d)>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Vend.Clash.names(~d, lc, hc, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Clash{}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  Merge.pick_facts.clash.at(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    W1,
    mc,
    %emc: {
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Work<Vend.L(d)>,
        _,
        cs => Work.set(~d, Work{lc, hc, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
      )
        == Some{W1}: Maybe<&2, Work<Vend.L(d)>>
    }
    e1,
    wc
  )

# what a pick of a merge gives the work: the ledger of the nodes that it has,
# and nodes that come after those before it
def Merge.pick_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  p: Pick,
  +W1: Work<Vend.L(d)>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match p:
    case Pick.Take{x}:
      Merge.set_facts(~d, l, lc, hc, P, Vend.Key.res(n), Vend.Res.value(x), W1, e1, wc)
    case Pick.Make{+h, +bytes}:
      Merge.pick_facts.make(
        ~d,
        l,
        lc,
        P,
        Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)),
        W1,
        Merge.set_facts(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Vend.Key.res(n),
          Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          W1,
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc)
        )
      )
    case Pick.Clash{}:
      Merge.pick_facts.clash(~d, l, lc, hc, P, k, n, W1, Vend.Clash.names(~d, lc, hc, k), {==}, e1, wc)

# the tree of the work after a take reads the resource as taken
def Merge.take_hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: Maybe<&2, Requests.Res>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Take{x}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n)) == Trees.Look.of(Vend.Res.value(x)): Trees.Look
}:
  Merge.writes_hit(
    ~d,
    lf,
    Merge.root(~d, W1),
    hc,
    Vend.Key.res(n),
    Vend.Res.value(x),
    Merge.set_core(
      ~d,
      l,
      lc,
      hc,
      P,
      Vend.Key.res(n),
      Vend.Res.value(x),
      lf,
      N,
      W1,
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Vend.Key.res(n), Vend.Res.value(x)),
      {==},
      e1,
      wc,
      wf,
      held,
      nd
    )
  )

# a pick that clashes leaves the key of a resource as it was, once the clashes
# that are open are read (mc)
def Merge.pick_frame.clash.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<Vend.L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<Vend.L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match mc:
    case None{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, eb)
      )
    case Some{+cs}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Vend.Key.clashes(k),
        Vend.Clash.value(Vend.Clash.put(n, cs)),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Vend.Key.clashes(k),
          Vend.Clash.value(Vend.Clash.put(n, cs)),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs))),
          {==},
          eb,
          wc,
          wf,
          held,
          nd
        ),
        Vend.Key.res(n0),
        v,
        {==},
        kn
      )

# what a pick of a merge does to the key of a resource n0 that it does not
# write: it reads as it did
def Merge.pick_frame(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  p: Pick,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Shared.List.is_eq(~U32, ~U32.is_eq, Vend.Key.res(n), Vend.Key.res(n0)) == False{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match p:
    case Pick.Take{+x}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Vend.Key.res(n),
        Vend.Res.value(x),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Vend.Key.res(n),
          Vend.Res.value(x),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Vend.Key.res(n), Vend.Res.value(x)),
          {==},
          e1,
          wc,
          wf,
          held,
          nd
        ),
        Vend.Key.res(n0),
        v,
        hk,
        kn
      )
    case Pick.Make{+h, +bytes}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Vend.Key.res(n),
        Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
        Merge.set_core(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Vend.Key.res(n),
          Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          lf,
          N,
          W1,
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
            hc,
            Vend.Key.res(n),
            Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}})
          ),
          {==},
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc),
          wf,
          held,
          nd
        ),
        Vend.Key.res(n0),
        v,
        hk,
        kn
      )
    case Pick.Clash{}:
      Merge.pick_frame.clash.at(
        ~d,
        l,
        lc,
        hc,
        P,
        k,
        n,
        n0,
        W1,
        lf,
        N,
        Vend.Clash.names(~d, lc, hc, k),
        e1,
        wc,
        wf,
        held,
        nd,
        v,
        kn
      )

# Merge.one once the pick of the three reads is known (mp)
def Merge.one.p(
  ~d: Vend.Led(),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.bind(&2, Pick, Work<Vend.L(d)>, mp, p => Merge.pick(~d, w, k, n, p))

# Merge.one once the read of theirs is known (mt)
def Merge.one.t(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<Vend.L(d)>,
    mt,
    t => Merge.one.p(~d, w, k, n, Pick.merge(~d, l, b, o, t))
  )

# Merge.one once the read of ours is known (mo)
def Merge.one.o(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<Vend.L(d)>,
    mo,
    +o => Merge.one.t(~d, l, w, k, n, b, o, Vend.Res.find(~d, l, ht, n))
  )

# Merge.one once the read of the base is known (mb)
def Merge.one.b(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<Vend.L(d)>,
    mb,
    +b => Merge.one.o(~d, l, ht, w, k, n, b, Vend.Res.find(~d, l, ho, n))
  )

# the reads and the pick of a merge of a resource, that gave the work W1
def Merge.Read.p(
  ~d: Vend.Led(),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>,
  W1: Work<Vend.L(d)>
) -> Data:
  Sigma<&2, &2, Pick, p => Merge.And({mp == Some{p}: Maybe<&2, Pick>}, {Merge.pick(~d, w, k, n, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>})>

def Merge.Read.t(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<Vend.L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, t => Merge.And({mt == Some{t}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.p(~d, w, k, n, Pick.merge(~d, l, b, o, t), W1))>

def Merge.Read.o(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<Vend.L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, o => Merge.And({mo == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.t(~d, l, w, k, n, b, o, Vend.Res.find(~d, l, ht, n), W1))>

def Merge.Read.b(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<Vend.L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, b => Merge.And({mb == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.o(~d, l, ht, w, k, n, b, Vend.Res.find(~d, l, ho, n), W1))>

def Merge.read.p(
  ~d: Vend.Led(),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>,
  +W1: Work<Vend.L(d)>,
  e: {Merge.one.p(~d, w, k, n, mp) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.Read.p(~d, w, k, n, mp, W1):
  match mp:
    case None{}:
      Empty.absurd(Merge.Read.p(~d, w, k, n, None{}, W1), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e))
    case Some{+p}:
      (p, ({==}, e))

def Merge.read.t(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  e: {Merge.one.t(~d, l, w, k, n, b, o, mt) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.Read.t(~d, l, w, k, n, b, o, mt, W1):
  match mt:
    case None{}:
      Empty.absurd(Merge.Read.t(~d, l, w, k, n, b, o, None{}, W1), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e))
    case Some{+t}:
      (t, ({==}, Merge.read.p(~d, w, k, n, Pick.merge(~d, l, b, o, t), W1, e)))

def Merge.read.o(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  e: {Merge.one.o(~d, l, ht, w, k, n, b, mo) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.Read.o(~d, l, ht, w, k, n, b, mo, W1):
  match mo:
    case None{}:
      Empty.absurd(Merge.Read.o(~d, l, ht, w, k, n, b, None{}, W1), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e))
    case Some{+o}:
      (o, ({==}, Merge.read.t(~d, l, w, k, n, b, o, Vend.Res.find(~d, l, ht, n), W1, e)))

# the reads and the pick of a merge of a resource that gave the work W1
def Merge.read(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  e: {Merge.one.b(~d, l, ho, ht, w, k, n, mb) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.Read.b(~d, l, ho, ht, w, k, n, mb, W1):
  match mb:
    case None{}:
      Empty.absurd(Merge.Read.b(~d, l, ho, ht, w, k, n, None{}, W1), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, e))
    case Some{+b}:
      (b, ({==}, Merge.read.o(~d, l, ht, w, k, n, b, Vend.Res.find(~d, l, ho, n), W1, e)))

# what a merge of a resource gives the work: the ledger of the nodes that it
# has, and nodes that come after those before it
def Merge.one_facts.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<Vend.L(d)>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +wc: Merge.Puts(~d, l, lc, P),
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_facts(~d, l, lc, hc, P, k, n, p, W1, e, wc)

# what a merge of a resource that does not write the key of the resource n0
# does to it: nothing
def Merge.one_frame.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Shared.List.is_eq(~U32, ~U32.is_eq, Vend.Key.res(n), Vend.Key.res(n0)) == False{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_frame(~d, l, lc, hc, P, k, n, n0, p, W1, lf, N, e, wc, wf, held, nd, hk, v, kn)

# the merge of the same reads is the same pick
def Merge.merge_args(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  eb: {b == b0: Maybe<&2, Requests.Res>},
  eo: {o == o0: Maybe<&2, Requests.Res>},
  et: {t == t0: Maybe<&2, Requests.Res>}
) -> {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, o0, t0): Maybe<&2, Pick>}:
  %et: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, o0, _): Maybe<&2, Pick>}
  %eo: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, _, t): Maybe<&2, Pick>}
  %eb: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, _, o, t): Maybe<&2, Pick>}
  {==}

# the pick of a merge of a resource, as its premises say: the reads are those
# of the premises, so the pick is
def Merge.pick_same(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +p: Pick,
  +q: Pick,
  eb: {b == b0: Maybe<&2, Requests.Res>},
  eo: {o == o0: Maybe<&2, Requests.Res>},
  et: {t == t0: Maybe<&2, Requests.Res>},
  ep: {Pick.merge(~d, l, b, o, t) == Some{p}: Maybe<&2, Pick>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{q}: Maybe<&2, Pick>}
) -> {p == q: Pick}:
  Shared.Maybe.some_inj(
    Pick,
    p,
    q,
    Equal.trans(
      Maybe<&2, Pick>,
      Some{p},
      Pick.merge(~d, l, b, o, t),
      Some{q},
      Equal.sym(Maybe<&2, Pick>, Pick.merge(~d, l, b, o, t), Some{p}, ep),
      Equal.trans(
        Maybe<&2, Pick>,
        Pick.merge(~d, l, b, o, t),
        Pick.merge(~d, l, b0, o0, t0),
        Some{q},
        Merge.merge_args(~d, l, b, o, t, b0, o0, t0, eb, eo, et),
        hp
      )
    )
  )

# the tree of the work after the merge of the resource n reads it as taken,
# when its reads and its pick are those that the premises say
def Merge.one_hit.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  hb0: {mb == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n)) == Trees.Look.of(Vend.Res.value(x)): Trees.Look
}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.take_hit(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    x,
    W1,
    lf,
    N,
      %Merge.pick_same(
        ~d,
        l,
        b,
        o,
        t,
        b0,
        o0,
        t0,
        p,
        Pick.Take{x},
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          b,
          b0,
          Equal.trans(Maybe<&2, Maybe<&2, Requests.Res>>, Some{b}, mb, Some{b0}, Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, mb, Some{b}, eb), hb0)
        ),
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          o,
          o0,
          Equal.trans(
            Maybe<&2, Maybe<&2, Requests.Res>>,
            Some{o},
            Vend.Res.find(~d, l, ho, n),
            Some{o0},
            Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Vend.Res.find(~d, l, ho, n), Some{o}, eo),
            ho0
          )
        ),
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          t,
          t0,
          Equal.trans(
            Maybe<&2, Maybe<&2, Requests.Res>>,
            Some{t},
            Vend.Res.find(~d, l, ht, n),
            Some{t0},
            Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Vend.Res.find(~d, l, ht, n), Some{t}, et),
            ht0
          )
        ),
        ep,
        hp
      ): {Merge.pick(~d, Work{lc, hc, P}, k, n, _) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
      e,
    wc,
    wf,
    held,
    nd
  )

# the name of the key of a resource is the name
def Merge.key_name(+n: Resources.Name) -> {Res.name(Vend.Key.res(n)) == Some{n}: Maybe<&2, Resources.Name>}:
  Codes.Code.whole_read(
    ~Resources.Name,
    ~Resources.Name.code,
    ~Resources.Name.code.read,
    ~(x => r => Resources.Name.code_read(x, r)),
    n
  )

# a first word that is not zero is not the first word of the key of a resource
def Merge.head_nonzero(
  w: Word(32n),
  t: List<&2, U32>,
  +n: Resources.Name,
  nz: {Shared.Word.is_zero(32n, w) == False{}: Bool},
  hh: {Res.name(U32{w} <> t) == Some{n}: Maybe<&2, Resources.Name>}
) -> Empty:
  match w:
    case WCon{True{}, w2}:
      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
    case WCon{False{}, w2}:
      match w2:
        case WCon{True{}, w3}:
          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
        case WCon{False{}, w3}:
          match w3:
            case WCon{True{}, w4}:
              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
            case WCon{False{}, w4}:
              match w4:
                case WCon{True{}, w5}:
                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                case WCon{False{}, w5}:
                  match w5:
                    case WCon{True{}, w6}:
                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                    case WCon{False{}, w6}:
                      match w6:
                        case WCon{True{}, w7}:
                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                        case WCon{False{}, w7}:
                          match w7:
                            case WCon{True{}, w8}:
                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                            case WCon{False{}, w8}:
                              match w8:
                                case WCon{True{}, w9}:
                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                case WCon{False{}, w9}:
                                  match w9:
                                    case WCon{True{}, w10}:
                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                    case WCon{False{}, w10}:
                                      match w10:
                                        case WCon{True{}, w11}:
                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                        case WCon{False{}, w11}:
                                          match w11:
                                            case WCon{True{}, w12}:
                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                            case WCon{False{}, w12}:
                                              match w12:
                                                case WCon{True{}, w13}:
                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                case WCon{False{}, w13}:
                                                  match w13:
                                                    case WCon{True{}, w14}:
                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                    case WCon{False{}, w14}:
                                                      match w14:
                                                        case WCon{True{}, w15}:
                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                        case WCon{False{}, w15}:
                                                          match w15:
                                                            case WCon{True{}, w16}:
                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                            case WCon{False{}, w16}:
                                                              match w16:
                                                                case WCon{True{}, w17}:
                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                case WCon{False{}, w17}:
                                                                  match w17:
                                                                    case WCon{True{}, w18}:
                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                    case WCon{False{}, w18}:
                                                                      match w18:
                                                                        case WCon{True{}, w19}:
                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                        case WCon{False{}, w19}:
                                                                          match w19:
                                                                            case WCon{True{}, w20}:
                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                            case WCon{False{}, w20}:
                                                                              match w20:
                                                                                case WCon{True{}, w21}:
                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                case WCon{False{}, w21}:
                                                                                  match w21:
                                                                                    case WCon{True{}, w22}:
                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                    case WCon{False{}, w22}:
                                                                                      match w22:
                                                                                        case WCon{True{}, w23}:
                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                        case WCon{False{}, w23}:
                                                                                          match w23:
                                                                                            case WCon{True{}, w24}:
                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                            case WCon{False{}, w24}:
                                                                                              match w24:
                                                                                                case WCon{True{}, w25}:
                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                case WCon{False{}, w25}:
                                                                                                  match w25:
                                                                                                    case WCon{True{}, w26}:
                                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                    case WCon{False{}, w26}:
                                                                                                      match w26:
                                                                                                        case WCon{True{}, w27}:
                                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                        case WCon{False{}, w27}:
                                                                                                          match w27:
                                                                                                            case WCon{True{}, w28}:
                                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                            case WCon{False{}, w28}:
                                                                                                              match w28:
                                                                                                                case WCon{True{}, w29}:
                                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                case WCon{False{}, w29}:
                                                                                                                  match w29:
                                                                                                                    case WCon{True{}, w30}:
                                                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                    case WCon{False{}, w30}:
                                                                                                                      match w30:
                                                                                                                        case WCon{True{}, w31}:
                                                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                        case WCon{False{}, w31}:
                                                                                                                          match w31:
                                                                                                                            case WCon{True{}, w32}:
                                                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                            case WCon{False{}, w32}:
                                                                                                                              match w32:
                                                                                                                                case WCon{True{}, w33}:
                                                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                                case WCon{False{}, w33}:
                                                                                                                                  match w33:
                                                                                                                                    case WNil{}:
                                                                                                                                      Shared.Bool.true_ne_false(nz)

# a key that has a name is the key of that resource, once it is known whether
# its first word is zero (b)
def Merge.name_key.at(
  +w: Word(32n),
  +r: List<&2, U32>,
  +n: Resources.Name,
  +b: Bool,
  +eb: {Shared.Word.is_zero(32n, w) == b: Bool},
  +h: {Res.name(U32{w} <> r) == Some{n}: Maybe<&2, Resources.Name>}
) -> {U32{w} <> r == Vend.Key.res(n): List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(
        Word(32n),
        w,
        Word.zero(32n),
        Shared.Word.is_zero_eq(32n, w)(eb)
      ): {U32{_} <> r == Vend.Key.res(n): List<&2, U32>}
      %Codes.Code.whole_back(
        ~Resources.Name,
        ~Resources.Name.code,
        ~Resources.Name.code.read,
        r,
        n
      )(
        %Shared.Word.is_zero_eq(32n, w)(eb): {Res.name(U32{_} <> r) == Some{n}: Maybe<&2, Resources.Name>}
        h
      ): {U32{Word.zero(32n)} <> _ == Vend.Key.res(n): List<&2, U32>}
      {==}
    case False{}:
      Empty.absurd({U32{w} <> r == Vend.Key.res(n): List<&2, U32>}, Merge.head_nonzero(w, r, n, eb, h))

# a key that has a name is the key of the resource of that name
def Merge.name_key(
  y: List<&2, U32>,
  +n: Resources.Name
) -> {Res.name(y) == Some{n}: Maybe<&2, Resources.Name>} -> {y == Vend.Key.res(n): List<&2, U32>}:
  match y:
    case Nil{}:
      h => Empty.absurd({Nil{} == Vend.Key.res(n): List<&2, U32>}, Shared.Maybe.none_ne_some(Resources.Name, n, h))
    case Con{U32{+w}, +r}:
      h => Merge.name_key.at(w, r, n, Shared.Word.is_zero(32n, w), {==}, h)

# the work after the merge of the key x: the work, or what the merge of the
# resource that the key names gives
def Merge.next(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +w: Work<Vend.L(d)>,
  mn: Maybe<&2, Resources.Name>
) -> Maybe<&2, Work<Vend.L(d)>>:
  match mn:
    case None{}:
      Some{w}
    case Some{+n}:
      Merge.one(~d, l, hb, ho, ht, k, n, w)

# the work that Merge.all goes on with after the key x
def Merge.step(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  x: List<&2, U32>,
  +w: Work<Vend.L(d)>
) -> Maybe<&2, Work<Vend.L(d)>>:
  Maybe.default(
    &2,
    Maybe<&2, Work<Vend.L(d)>>,
    Maybe.bind(
      &2,
      Resources.Name,
      Maybe<&2, Work<Vend.L(d)>>,
      Res.name(x),
      n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
    ),
    Some{w}
  )

# a step is the work that the name of its key gives, once it is read (mn)
def Merge.step_eq.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +w: Work<Vend.L(d)>,
  mn: Maybe<&2, Resources.Name>
) -> {
  Maybe.default(
    &2,
    Maybe<&2, Work<Vend.L(d)>>,
    Maybe.bind(
      &2,
      Resources.Name,
      Maybe<&2, Work<Vend.L(d)>>,
      mn,
      n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
    ),
    Some{w}
  )
    == Merge.next(~d, l, hb, ho, ht, k, w, mn): Maybe<&2, Work<Vend.L(d)>>
}:
  match mn:
    case None{}:
      {==}
    case Some{+n}:
      {==}

# the work that a merge goes on with after a key is the next work
def Merge.step_eq(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  x: List<&2, U32>,
  +w: Work<Vend.L(d)>
) -> {Merge.step(~d, l, hb, ho, ht, k, x, w) == Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)): Maybe<&2, Work<Vend.L(d)>>}:
  Merge.step_eq.at(~d, l, hb, ho, ht, k, w, Res.name(x))

# a merge that gave a work went on with a work
def Merge.all_from(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  m: Maybe<&2, Work<Vend.L(d)>>,
  +Wf: Work<Vend.L(d)>,
  e: {Merge.all(~d, l, hb, ho, ht, k, xs, m) == Some{Wf}: Maybe<&2, Work<Vend.L(d)>>}
) -> Sigma<&2, &2, Work<Vend.L(d)>, W1 => {m == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}>:
  match xs m:
    case Nil{} y:
      (Wf, e)
    case Con{x, rest} None{}:
      Empty.absurd(
        Sigma<&2, &2, Work<Vend.L(d)>, W1 => {None{} == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}>,
        Shared.Maybe.none_ne_some(Work<Vend.L(d)>, Wf, e)
      )
    case Con{x, rest} Some{+w}:
      (w, {==})

# the merge of the key x went on, from the work w, with a work W1: the merge of
# the keys after it went on from W1 to Wf
def Merge.Stepped(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<Vend.L(d)>,
  +Wf: Work<Vend.L(d)>
) -> Data:
  Sigma<&2, &2, Work<Vend.L(d)>, W1 => Merge.And({Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Wf}: Maybe<&2, Work<Vend.L(d)>>}, {Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>})>

# a merge that went on after a key, from the work w, went on with the work W1
def Merge.all_step.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<Vend.L(d)>,
  +Wf: Work<Vend.L(d)>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, x <> rest, Some{w}) == Some{Wf}: Maybe<&2, Work<Vend.L(d)>>},
  sg: Sigma<&2, &2, Work<Vend.L(d)>, W1 => {Merge.step(~d, l, hb, ho, ht, k, x, w) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}>
) -> Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, w, Wf):
  (+W1, +es) = sg
  (
    W1,
    (
      %es: {Merge.all(~d, l, hb, ho, ht, k, rest, _) == Some{Wf}: Maybe<&2, Work<Vend.L(d)>>}
      e,
      Equal.trans(
        Maybe<&2, Work<Vend.L(d)>>,
        Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)),
        Merge.step(~d, l, hb, ho, ht, k, x, w),
        Some{W1},
        Equal.sym(
          Maybe<&2, Work<Vend.L(d)>>,
          Merge.step(~d, l, hb, ho, ht, k, x, w),
          Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)),
          Merge.step_eq(~d, l, hb, ho, ht, k, x, w)
        ),
        es
      )
    )
  )

# a merge that went on after a key went on with a work
def Merge.all_step(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<Vend.L(d)>,
  +Wf: Work<Vend.L(d)>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, x <> rest, Some{w}) == Some{Wf}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, w, Wf):
  Merge.all_step.at(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    x,
    rest,
    w,
    Wf,
    e,
    Merge.all_from(~d, l, hb, ho, ht, k, rest, Merge.step(~d, l, hb, ho, ht, k, x, w), Wf, e)
  )

# the first of a pair of Data
def Merge.And.left(-A: Data, -B: Data, p: Merge.And(A, B)) -> A:
  match p:
    case Tuple{a, b}:
      a

# the second of a pair of Data
def Merge.And.right(-A: Data, -B: Data, p: Merge.And(A, B)) -> B:
  match p:
    case Tuple{a, b}:
      b

# what the next merge gives the work: the ledger of the nodes that it has, and
# nodes that come after those before it
def Merge.next_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<Vend.L(d)>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, W1, e): Merge.And(
        Merge.Puts(~d, l, Merge.ledger(~d, _), Merge.nodes(~d, _)),
        Merge.Nodes(P, Merge.nodes(~d, _))
      )
      (wc, Merge.nodes_refl(P))
    case Some{+n}:
      Merge.one_facts.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        W1,
        Vend.Res.find(~d, l, hb, n),
        wc,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e)
      )

# the merge of the key of a name writes no other key than the key of that name
def Merge.apart(mn: Maybe<&2, Resources.Name>, n0: Resources.Name) -> Bool:
  match mn:
    case None{}:
      True{}
    case Some{n}:
      Bool.not(Shared.List.is_eq(~U32, ~U32.is_eq, Vend.Key.res(n), Vend.Key.res(n0)))

# the tree of the work after the next merge reads the key of a resource n0 as
# it did, when the merge does not write it
def Merge.next_frame(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Merge.apart(mn, n0) == True{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, W1, e): {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, _), Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      kn
    case Some{+n}:
      Merge.one_frame.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        n0,
        Vend.Res.find(~d, l, hb, n),
        W1,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
        lf,
        N,
        wc,
        wf,
        held,
        nd,
        Shared.Bool.not_true(Shared.List.is_eq(~U32, ~U32.is_eq, Vend.Key.res(n), Vend.Key.res(n0)))(hk),
        v,
        kn
      )

# the tree of the work after the next merge of the resource n reads it as taken,
# when the reads and the pick are those that the premises say
def Merge.next_hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n)) == Trees.Look.of(Vend.Res.value(x)): Trees.Look
}:
  Merge.one_hit.at(
    ~d,
    l,
    lc,
    ho,
    ht,
    hc,
    P,
    k,
    n,
    b0,
    o0,
    t0,
    x,
    Vend.Res.find(~d, l, hb, n),
    W1,
    Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
    hb0,
    ho0,
    ht0,
    hp,
    lf,
    N,
    wc,
    wf,
    held,
    nd
  )

# two merges that end in the same work end in the same ledger and the same
# nodes
def Merge.work_eq(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>}
) -> Merge.And({lc == lf: Vend.L(d)}, Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>})):
  (
    Equal.cong(
      Work<Vend.L(d)>,
      Vend.L(d),
      w => Merge.ledger(~d, w),
      Work{lc, hc, P},
      Work{lf, hf, N},
      Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
    ),
    (
      Equal.cong(
        Work<Vend.L(d)>,
        Maybe<&2, Hashes.Hash>,
        w => Merge.root(~d, w),
        Work{lc, hc, P},
        Work{lf, hf, N},
        Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
      ),
      Equal.cong(
        Work<Vend.L(d)>,
        List<&2, List<&2, U32>>,
        w => Merge.nodes(~d, w),
        Work{lc, hc, P},
        Work{lf, hf, N},
        Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
      )
    )
  )

# two merges that end in the same work end in the same tree
def Merge.work_eq.root(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>}
) -> {hc == hf: Maybe<&2, Hashes.Hash>}:
  Equal.cong(
    Work<Vend.L(d)>,
    Maybe<&2, Hashes.Hash>,
    w => Merge.root(~d, w),
    Work{lc, hc, P},
    Work{lf, hf, N},
    Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
  )

# two merges that end in the same work end in the same nodes
def Merge.work_eq.nodes(
  ~d: Vend.Led(),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>}
) -> {P == N: List<&2, List<&2, U32>>}:
  Equal.cong(
    Work<Vend.L(d)>,
    List<&2, List<&2, U32>>,
    w => Merge.nodes(~d, w),
    Work{lc, hc, P},
    Work{lf, hf, N},
    Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
  )

# the induction hypothesis of Merge.all_puts for the keys rest
def Merge.PutsIH(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  rest: List<&2, List<&2, U32>>,
  lf: Vend.L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: Vend.L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P1, N))

# the work of a merge is the ledger of its nodes, and its nodes come after those
# of the work before, from the facts of a step and of the rest
def Merge.all_puts.fin(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc1: Vend.L(d),
  +lf: Vend.L(d),
  +P: List<&2, List<&2, U32>>,
  +P1: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  facts: Merge.And(Merge.Puts(~d, l, lc1, P1), Merge.Nodes(P, P1)),
  ihres: Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P1, N))
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  (+a, nd1) = facts
  (+b, nd2) = ihres
  (b, Merge.nodes_trans(P, P1, N, nd1, nd2))

# Merge.all_puts for the keys x then rest, once the work W1 after the first step
# is known
def Merge.all_puts.con2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  W1: Work<Vend.L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  ih: Merge.PutsIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  match W1:
    case Work{+lc1, +hc1, +P1}:
      Merge.all_puts.fin(
        ~d,
        l,
        lc1,
        lf,
        P,
        P1,
        N,
        Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc),
        ih(lc1)(hc1)(P1)(erest)(
          Merge.And.left(
            Merge.Puts(~d, l, lc1, P1),
            Merge.Nodes(P, P1),
            Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
          )
        )
      )

# Merge.all_puts for the keys x then rest, once the first step is known
def Merge.all_puts.con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.PutsIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_puts.con2(~d, l, hb, ho, ht, k, x, rest, lc, hc, P, lf, hf, N, wc, W1, erest, enext, ih)

# a merge ends in the ledger of its nodes, and its nodes come after those of
# the work that it starts from
def Merge.all_puts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  match xs:
    case Nil{}:
      %Merge.And.left(
        {lc == lf: Vend.L(d)},
        Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>}),
        Merge.work_eq(~d, lc, hc, P, lf, hf, N, e)
      ): Merge.And(Merge.Puts(~d, l, _, N), Merge.Nodes(P, N))
      %Merge.And.right(
        {hc == hf: Maybe<&2, Hashes.Hash>},
        {P == N: List<&2, List<&2, U32>>},
        Merge.And.right(
          {lc == lf: Vend.L(d)},
          Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>}),
          Merge.work_eq(~d, lc, hc, P, lf, hf, N, e)
        )
      ): Merge.And(Merge.Puts(~d, l, lc, _), Merge.Nodes(P, _))
      (wc, Merge.nodes_refl(P))
    case Con{+x, +rest}:
      Merge.all_puts.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => Merge.all_puts(~d, l, hb, ho, ht, k, rest, lc1, hc1, P1, lf, hf, N, e1, wc1)
      )

# the merge of the key x writes no key but x, once its name is read (mn)
def Merge.apart_of.at(
  +x: List<&2, U32>,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  emn: {Res.name(x) == mn: Maybe<&2, Resources.Name>},
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n0)) == False{}: Bool}
) -> {Merge.apart(mn, n0) == True{}: Bool}:
  match mn:
    case None{}:
      {==}
    case Some{+n}:
      %Merge.name_key(x, n)(emn): {Bool.not(Shared.List.is_eq(~U32, ~U32.is_eq, _, Vend.Key.res(n0))) == True{}: Bool}
      %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n0)), False{}, hx): {Bool.not(_) == True{}: Bool}
      {==}

# the merge of a key other than the key of a resource writes no key but its own
def Merge.apart_of(
  +x: List<&2, U32>,
  +n0: Resources.Name,
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n0)) == False{}: Bool}
) -> {Merge.apart(Res.name(x), n0) == True{}: Bool}:
  Merge.apart_of.at(x, n0, Res.name(x), {==}, hx)

# a key is not in the keys x then rest, once it is known whether it is x (p)
def Merge.cons_false.at(
  +p: Bool,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  h: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K), p) == False{}: Bool
  }
) -> Merge.And(
  {p == False{}: Bool},
  {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
):
  match p:
    case True{}:
      Empty.absurd(
        Merge.And(
          {True{} == False{}: Bool},
          {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
        ),
        Shared.Bool.true_ne_false(h)
      )
    case False{}:
      ({==}, h)

# a key that is not in the keys x then rest is not x, and is not in rest
def Merge.cons_false(
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  h: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, K) == False{}: Bool}
) -> Merge.And(
  {Shared.List.is_eq(~U32, ~U32.is_eq, x, K) == False{}: Bool},
  {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
):
  Merge.cons_false.at(Shared.List.is_eq(~U32, ~U32.is_eq, x, K), rest, K, h)

# the induction hypothesis of Merge.all_frame for the keys rest
def Merge.FrameIH(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>,
  lf: Vend.L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: Vend.L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n0)) == False{}: Bool
  } -> {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc1, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# Merge.all_frame for the keys x then rest, once the work W1 after the first
# step is known
def Merge.all_frame.con2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, Vend.Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  W1: Work<Vend.L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  ih: Merge.FrameIH(~d, l, hb, ho, ht, k, n0, v, rest, lf, hf, N)
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match W1:
    case Work{+lc1, +hc1, +P1}:
      ih(lc1)(hc1)(P1)(erest)(
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
        )
      )(
        Merge.And.right(
          {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n0)) == False{}: Bool},
          {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n0)) == False{}: Bool},
          Merge.cons_false(x, rest, Vend.Key.res(n0), hx)
        )
      )(
        Merge.next_frame(
          ~d,
          l,
          lc,
          hb,
          ho,
          ht,
          hc,
          P,
          k,
          n0,
          Res.name(x),
          Work{lc1, hc1, P1},
          lf,
          N,
          enext,
          wc,
          wf,
          held,
          Merge.And.right(
            Merge.Puts(~d, l, lf, N),
            Merge.Nodes(P1, N),
            Merge.all_puts(
              ~d,
              l,
              hb,
              ho,
              ht,
              k,
              rest,
              lc1,
              hc1,
              P1,
              lf,
              hf,
              N,
              erest,
              Merge.And.left(
                Merge.Puts(~d, l, lc1, P1),
                Merge.Nodes(P, P1),
                Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
              )
            )
          ),
          Merge.apart_of(
            x,
            n0,
            Merge.And.left(
              {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n0)) == False{}: Bool},
              {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n0)) == False{}: Bool},
              Merge.cons_false(x, rest, Vend.Key.res(n0), hx)
            )
          ),
          v,
          kn
        )
      )

# Merge.all_frame for the keys x then rest, once the first step is known
def Merge.all_frame.con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, Vend.Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.FrameIH(~d, l, hb, ho, ht, k, n0, v, rest, lf, hf, N)
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_frame.con2(~d, l, hb, ho, ht, k, n0, v, x, rest, lc, hc, P, lf, hf, N, wc, wf, held, hx, kn, W1, erest, enext, ih)

# a merge of keys among which is not the key of a resource leaves what it reads
# as it was
def Merge.all_frame(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  xs: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), xs, Vend.Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match xs:
    case Nil{}:
      %Merge.work_eq.root(~d, lc, hc, P, lf, hf, N, e): {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, _, Vend.Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      kn
    case Con{+x, +rest}:
      Merge.all_frame.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n0,
        v,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hx,
        kn,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => hx1 => kn1 => Merge.all_frame(~d, l, hb, ho, ht, k, n0, v, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hx1, kn1)
      )

# a read that finds a value is known, once the value is the written one
def Merge.known_look(
  m: Maybe<&2, List<&2, U32>>
) -> {Trees.Look.known(Trees.Look.of(m)) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

# a read that is the read of a written value is known as that value
def Merge.known_of(
  l: Trees.Look,
  m: Maybe<&2, List<&2, U32>>,
  e: {l == Trees.Look.of(m): Trees.Look}
) -> {Trees.Look.known(l) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  %Equal.sym(Trees.Look, l, Trees.Look.of(m), e): {Trees.Look.known(_) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
  Merge.known_look(m)

# the key y is the key of the resource n, once it is known that it is the key
def Merge.name_of_key(
  +y: List<&2, U32>,
  +n: Resources.Name,
  e: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Vend.Key.res(n)) == True{}: Bool}
) -> {Res.name(y) == Some{n}: Maybe<&2, Resources.Name>}:
  %Equal.sym(
    List<&2, U32>,
    y,
    Vend.Key.res(n),
    Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), y, Vend.Key.res(n))(e)
  ): {Res.name(_) == Some{n}: Maybe<&2, Resources.Name>}
  Merge.key_name(n)

# the induction hypothesis of Merge.all_take for the keys rest
def Merge.TakeIH(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: Maybe<&2, Requests.Res>,
  rest: List<&2, List<&2, U32>>,
  lf: Vend.L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: Vend.L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)) == True{}: Bool
  } -> {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }

# Merge.all_take once the key y is the key of the resource n, and no key after
# it is
def Merge.all_take.hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +lc1: Vend.L(d),
  +hc1: Maybe<&2, Hashes.Hash>,
  +P1: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wc1: Merge.Puts(~d, l, lc1, P1),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ey: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Vend.Key.res(n)) == True{}: Bool},
  +erest: {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  },
  +enext: {
    Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<Vend.L(d)>>
  },
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)) == False{}: Bool}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  Merge.all_frame(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    Vend.Res.value(x),
    rest,
    lc1,
    hc1,
    P1,
    lf,
    hf,
    N,
    erest,
    wc1,
    wf,
    held,
    ec,
    Merge.known_of(
      Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, hc1, Vend.Key.res(n)),
      Vend.Res.value(x),
      Merge.next_hit(
        ~d,
        l,
        lc,
        hb,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        Work{lc1, hc1, P1},
        lf,
        N,
        %Merge.name_of_key(y, n, ey): {
          Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, _) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<Vend.L(d)>>
        }
        enext,
        hb0,
        ho0,
        ht0,
        hp,
        wc,
        wf,
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes(P1, N),
          Merge.all_puts(~d, l, hb, ho, ht, k, rest, lc1, hc1, P1, lf, hf, N, erest, wc1)
        )
      )
    )
  )

# Merge.all_take once it is known whether the key y is the key of the resource
# n (p), and whether the keys after it hold it (c)
def Merge.all_take.cc(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +lc1: Vend.L(d),
  +hc1: Maybe<&2, Hashes.Hash>,
  +P1: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wc1: Merge.Puts(~d, l, lc1, P1),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +erest: {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  },
  +enext: {
    Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<Vend.L(d)>>
  },
  +p: Bool,
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Vend.Key.res(n)) == p: Bool},
  +c: Bool,
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)) == c: Bool},
  +hx: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)), p) == True{}: Bool
  },
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match p c:
    case q True{}:
      ih(lc1)(hc1)(P1)(erest)(wc1)(ec)
    case True{} False{}:
      Merge.all_take.hit(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        lc1,
        hc1,
        P1,
        wc,
        wc1,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        ep,
        erest,
        enext,
        ec
      )
    case False{} False{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)),
            True{},
            Equal.sym(
              Bool,
              List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)),
              False{},
              ec
            ),
            hx
          )
        )
      )
# Merge.all_take for the keys y then rest, once the work W1 after the first step
# is known
def Merge.all_take.con2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), y <> rest, Vend.Key.res(n)) == True{}: Bool},
  W1: Work<Vend.L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match W1:
    case Work{+lc1, +hc1, +P1}:
      Merge.all_take.cc(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        lc1,
        hc1,
        P1,
        wc,
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(y), Work{lc1, hc1, P1}, enext, wc)
        ),
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        erest,
        enext,
        Shared.List.is_eq(~U32, ~U32.is_eq, y, Vend.Key.res(n)),
        {==},
        List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)),
        {==},
        hx,
        ih
      )

# Merge.all_take for the keys y then rest, once the first step is known
def Merge.all_take.con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), y <> rest, Vend.Key.res(n)) == True{}: Bool},
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, y, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_take.con2(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    b0,
    o0,
    t0,
    x,
    y,
    rest,
    lc,
    hc,
    P,
    lf,
    hf,
    N,
    wc,
    wf,
    held,
    hb0,
    ho0,
    ht0,
    hp,
    hx,
    W1,
    erest,
    enext,
    ih
  )

# a merge of keys among which is the key of a resource, whose merge takes a
# side, reads the resource as that side
def Merge.all_take(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  xs: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), xs, Vend.Key.res(n)) == True{}: Bool}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match xs:
    case Nil{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Vend.Key.res(n)) == Some{Vend.Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(hx)
      )
    case Con{+y, +rest}:
      Merge.all_take.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        hx,
        Merge.all_step(~d, l, hb, ho, ht, k, y, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => ec => Merge.all_take(~d, l, hb, ho, ht, k, n, b0, o0, t0, x, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hb0, ho0, ht0, hp, ec)
      )
# the resource that a resource of the tree holds as a value is the resource
def Merge.found_value(+x: Maybe<&2, Requests.Res>) -> {Vend.Res.found(Vend.Res.value(x)) == x: Maybe<&2, Requests.Res>}:
  match x:
    case None{}:
      {==}
    case Some{+r}:
      Codes.Code.whole_read(
        ~Requests.Res,
        ~Requests.Res.code,
        ~Requests.Res.code.read,
        ~(a => s => Requests.Res.code_read(a, s)),
        r
      )

# a read that finds a value finds the resource that the value holds
def Merge.find_res(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  v: Maybe<&2, List<&2, U32>>,
  e: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Vend.Res.find(~d, l, h, n) == Some{Vend.Res.found(v)}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(n)),
    Some{v},
    e
  ): {
    Maybe.bind(
      &2,
      Maybe<&2, List<&2, U32>>,
      Maybe<&2, Requests.Res>,
      _,
      m => Some{Vend.Res.found(m)}
    )
      == Some{Vend.Res.found(v)}: Maybe<&2, Maybe<&2, Requests.Res>>
  }
  {==}

# a read of a resource found the resource that a value holds
def Merge.Found(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>
) -> Data:
  Sigma<&2, &2, Maybe<&2, List<&2, U32>>, v => Merge.And({Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, {Vend.Res.found(v) == o: Maybe<&2, Requests.Res>})>

# a resource that a read finds is the resource that the value found holds, once
# the read is known (m)
def Merge.find_some.at(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(n)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {
    Maybe.bind(&2, Maybe<&2, List<&2, U32>>, Maybe<&2, Requests.Res>, m, v => Some{Vend.Res.found(v)})
      == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
  }
) -> Merge.Found(~d, l, h, n, o):
  match m:
    case None{}:
      Empty.absurd(
        Merge.Found(~d, l, h, n, o),
        Shared.Maybe.none_ne_some(Maybe<&2, Requests.Res>, o, e)
      )
    case Some{+v}:
      (v, (em, Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Vend.Res.found(v), o, e)))
# a resource that a read finds is the resource that the value found holds
def Merge.find_some(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  e: {Vend.Res.find(~d, l, h, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
) -> Merge.Found(~d, l, h, n, o):
  Merge.find_some.at(~d, l, h, n, o, Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(n)), {==}, e)

# the value that a read finds is the value that it is known as
def Merge.value_known(
  r: Trees.Look,
  m: Maybe<&2, List<&2, U32>>,
  e: {Trees.Look.known(r) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Trees.Look.value(r) == m: Maybe<&2, List<&2, U32>>}:
  match r:
    case Trees.Look.Found{+v}:
      Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{v}, m, e)
    case Trees.Look.Absent{}:
      Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, m, e)
    case Trees.Look.Missing{h}:
      Empty.absurd({Trees.Look.value(Trees.Look.Missing{h}) == m: Maybe<&2, List<&2, U32>>}, Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, m, e))

# a resource is the same as itself
def Merge.same_refl(+a: Maybe<&2, Requests.Res>) -> {Vend.Res.same(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{+r}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Requests.Res.code(r, []))

# the resource that a pick takes
def Merge.pick_res(p: Pick) -> Maybe<&2, Requests.Res>:
  match p:
    case Pick.Take{r}:
      r
    case _:
      None{}

# a merge that takes a side, of two sides that are the same, takes them
def Merge.take_value.at(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  s: Sides.Side,
  es: {Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th) == s: Sides.Side},
  hp: {Pick.side(~d, l, b, o, th, s) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  eoth: {o == th: Maybe<&2, Requests.Res>}
) -> {x == o: Maybe<&2, Requests.Res>}:
  match s:
    case Sides.Side.Theirs{}:
      Equal.trans(
        Maybe<&2, Requests.Res>,
        x,
        th,
        o,
        Equal.sym(
          Maybe<&2, Requests.Res>,
          th,
          x,
          Equal.cong(
            Pick,
            Maybe<&2, Requests.Res>,
            q => Merge.pick_res(q),
            Pick.Take{th},
            Pick.Take{x},
            Shared.Maybe.some_inj(Pick, Pick.Take{th}, Pick.Take{x}, hp)
          )
        ),
        Equal.sym(Maybe<&2, Requests.Res>, o, th, eoth)
      )
    case Sides.Side.Ours{}:
      Equal.sym(
        Maybe<&2, Requests.Res>,
        o,
        x,
        Equal.cong(
          Pick,
          Maybe<&2, Requests.Res>,
          q => Merge.pick_res(q),
          Pick.Take{o},
          Pick.Take{x},
          Shared.Maybe.some_inj(Pick, Pick.Take{o}, Pick.Take{x}, hp)
        )
      )
    case Sides.Side.Both{}:
      Empty.absurd(
        {x == o: Maybe<&2, Requests.Res>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Bool.or(Vend.Res.same(o, b), Bool.or(Vend.Res.same(th, b), Vend.Res.same(o, th))),
            True{},
            Equal.sym(
              Bool,
              Bool.or(Vend.Res.same(o, b), Bool.or(Vend.Res.same(th, b), Vend.Res.same(o, th))),
              False{},
              Sides.Side.both_changed(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th)(es)
            ),
            %Equal.sym(
              Bool,
              Bool.or(Vend.Res.same(th, b), Vend.Res.same(o, th)),
              True{},
              %Equal.sym(
                Bool,
                Vend.Res.same(o, th),
                True{},
                %eoth: {Vend.Res.same(o, _) == True{}: Bool}
                Merge.same_refl(o)
              ): {Bool.or(Vend.Res.same(th, b), _) == True{}: Bool}
              Shared.Bool.or_true_right(Vend.Res.same(th, b))
            ): {Bool.or(Vend.Res.same(o, b), _) == True{}: Bool}
            Shared.Bool.or_true_right(Vend.Res.same(o, b))
          )
        )
      )

# a merge that takes a side, of two sides that are the same, takes them
def Merge.take_value(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  eoth: {o == th: Maybe<&2, Requests.Res>}
) -> {x == o: Maybe<&2, Requests.Res>}:
  Merge.take_value.at(~d, l, b, o, th, x, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th), {==}, hp, eoth)
# the second of a pair
def Merge.snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case Tuple{a, b}:
      b

# the law of a difference, of the tree of the ledger d
def Merge.laws_diff(d: Vend.Led()) -> Trees.Laws.Diff(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, Tuple{df, rest}}}}}}}}:
      df

# the law of the trees that the ledger d holds whole
def Merge.laws_whole(d: Vend.Led()) -> Trees.Laws.Whole(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, Tuple{df, Tuple{wh, kp}}}}}}}}}:
      wh

# two whole trees differ, by the law of a tree
def Merge.whole_diff(
  -S: Data,
  -o: Trees.Tree.Ops(S),
  wh: Trees.Laws.Whole(S, o),
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  bs: List<&2, Trees.Binding>,
  bs2: List<&2, Trees.Binding>,
  e1: {Trees.Ops.range(S, o)(s)(h)([]) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  e2: {Trees.Ops.range(S, o)(s)(h2)([]) == Some{bs2}: Maybe<&2, List<&2, Trees.Binding>>}
) -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Trees.Ops.diff(S, o)(s)(h)(h2)) == True{}: Bool}:
  match wh:
    case Tuple{empty, w2}:
      Merge.snd(
        (@k: List<&2, U32> -> @m: Maybe<&2, List<&2, U32>> -> @p: List<&2, U32> -> {
          Trees.Look.is_final(Trees.Ops.look(S, o)(s)(h)(k)) == True{}: Bool
        }
          & (
            {Maybe.is_some(&2, Trees.Edit, Trees.Ops.put(S, o)(s)(h)(k)(m)) == True{}: Bool}
              & {Maybe.is_some(&2, List<&2, Trees.Binding>, Trees.Ops.range(S, o)(s)(h)(p)) == True{}: Bool}
          )),
        (@h3: Maybe<&2, Hashes.Hash> -> @bs3: List<&2, Trees.Binding> -> {
          Trees.Ops.range(S, o)(s)(h3)([]) == Some{bs3}: Maybe<&2, List<&2, Trees.Binding>>
        } -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Trees.Ops.diff(S, o)(s)(h)(h3)) == True{}: Bool}),
        w2(s)(h)(bs)(e1)
      )(h2)(bs2)(e2)

# the tree whose root is h lists whole, once it is kept
def Merge.kept_range.at(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, List<&2, Trees.Binding>>,
  em: {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == m: Maybe<&2, List<&2, Trees.Binding>>},
  e: {
    Maybe.default(
      &2,
      Bool,
      Maybe.bind(&2, List<&2, Trees.Binding>, Bool, m, bs => Some{Vend.Res.all_held(~d, l, bs)}),
      False{}
    )
      == True{}: Bool
  }
) -> Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>:
  match m:
    case None{}:
      Empty.absurd(
        Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>,
        Shared.Bool.false_ne_true(e)
      )
    case Some{+bs}:
      (bs, em)

# a tree that is kept lists whole
def Merge.kept_range(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  e: {Vend.Tree.kept(~d, l, h) == True{}: Bool}
) -> Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>:
  Merge.kept_range.at(~d, l, h, Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []), {==}, e)
# the root that an act takes
def Merge.act_root(a: Replicas.Act) -> Maybe<&2, Hashes.Hash>:
  match a:
    case Replicas.Act.Taken{vs, h, ns}:
      h
    case _:
      None{}

# the nodes that an act takes
def Merge.act_nodes(a: Replicas.Act) -> List<&2, List<&2, U32>>:
  match a:
    case Replicas.Act.Taken{vs, h, ns}:
      ns
    case _:
      []

# the act of a work, once it is known whether the ledger of the work holds its
# nodes (p)
def Merge.work_act.at(
  ~d: Vend.Led(),
  +lw: Vend.L(d),
  +hw: Maybe<&2, Hashes.Hash>,
  +nsw: List<&2, List<&2, U32>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +p: Bool,
  +ep: {
    Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lw, nsw) == p: Bool
  },
  +e: {
    Shared.Maybe.when(Replicas.Act, p, u => Some{Replicas.Act.Taken{None{}, hw, nsw}})
      == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
  }
) -> Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw))):
  match p:
    case True{}:
      (
        Equal.cong(
          Replicas.Act,
          Maybe<&2, Hashes.Hash>,
          a => Merge.act_root(a),
          Replicas.Act.Taken{None{}, hw, nsw},
          Replicas.Act.Taken{vs, h2, ns},
          Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{None{}, hw, nsw}, Replicas.Act.Taken{vs, h2, ns}, e)
        ),
        (
          Equal.cong(
            Replicas.Act,
            List<&2, List<&2, U32>>,
            a => Merge.act_nodes(a),
            Replicas.Act.Taken{None{}, hw, nsw},
            Replicas.Act.Taken{vs, h2, ns},
            Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{None{}, hw, nsw}, Replicas.Act.Taken{vs, h2, ns}, e)
          ),
          ep
        )
      )
    case False{}:
      Empty.absurd(
        Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw))),
        Shared.Maybe.none_ne_some(Replicas.Act, Replicas.Act.Taken{vs, h2, ns}, e)
      )

# the work that an act is of: its root and nodes are those of the act, and its
# ledger holds its nodes
def Merge.Acted(
  ~d: Vend.Led(),
  m: Maybe<&2, Work<Vend.L(d)>>,
  h2: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>
) -> Data:
  Sigma<&2, &2, Work<Vend.L(d)>, W => Merge.And({m == Some{W}: Maybe<&2, Work<Vend.L(d)>>}, Merge.And({Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>}, Merge.And({Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)))))>

# the facts of the act of a work give the work that the act is of
def Merge.work_act.acted(
  ~d: Vend.Led(),
  +lw: Vend.L(d),
  +hw: Maybe<&2, Hashes.Hash>,
  +nsw: List<&2, List<&2, U32>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  f: Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw)))
) -> Merge.Acted(~d, Some{Work{lw, hw, nsw}}, h2, ns):
  (+a, r1) = f
  (+b, held) = r1
  (Work{lw, hw, nsw}, ({==}, (a, (b, held))))

# the act that takes a work is taken, with the nodes of the work, once the work
# is known
def Merge.work_act(
  ~d: Vend.Led(),
  m: Maybe<&2, Work<Vend.L(d)>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  e: {Work.act(~d, None{}, m) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Acted(~d, m, h2, ns):
  match m:
    case None{}:
      Empty.absurd(Merge.Acted(~d, None{}, h2, ns), Shared.Maybe.none_ne_some(Replicas.Act, Replicas.Act.Taken{vs, h2, ns}, e))
    case Some{Work{+lw, +hw, +nsw}}:
      Merge.work_act.acted(
        ~d,
        lw,
        hw,
        nsw,
        h2,
        ns,
        Merge.work_act.at(
          ~d,
          lw,
          hw,
          nsw,
          vs,
          h2,
          ns,
          Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lw, nsw),
          {==},
          e
        )
      )
# that the three trees of a merge are whole
def Merge.ok(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>
) -> Bool:
  List.all.if(u => List.all.if(u2 => Vend.Tree.kept(~d, l, ho), Vend.Tree.kept(~d, l, hb)), Vend.Tree.kept(~d, l, ht))

# the act of a merge once the trees are checked (ok) and the keys to merge are
# read (md)
def Merge.act.go(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ok: Bool,
  md: Maybe<&2, List<&2, List<&2, U32>>>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    ok,
    u => Work.act(
      ~d,
      None{},
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        Maybe.default(&2, List<&2, List<&2, U32>>, md, []),
        Some{Work{l, ho, []}}
      )
    ),
    u => None{}
  )

# the act of a merge is the act once its trees are checked
def Merge.act_eq(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  t: Replicas.Tip,
  +k: Ledgers.Id,
  from: Requests.Source,
  base: Maybe<&2, Requests.Source>
) -> {
  Merge.act(~d, l, t, k, from, base)
    == Merge.act.go(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Vend.Source.root(from),
      Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from))
    ): Maybe<&2, Replicas.Act>
}:
  {==}

# a merge that gives an act has its trees checked
def Merge.act_ok(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ok: Bool,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  ac: Replicas.Act,
  e: {Merge.act.go(~d, l, k, hb, ho, ht, ok, md) == Some{ac}: Maybe<&2, Replicas.Act>}
) -> {ok == True{}: Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Replicas.Act, ac, e))

# the three trees that a check holds of are each kept
def Merge.guard3(
  a: Bool,
  b: Bool,
  c: Bool,
  h: {List.all.if(u => List.all.if(u2 => c, b), a) == True{}: Bool}
) -> Merge.And({a == True{}: Bool}, Merge.And({b == True{}: Bool}, {c == True{}: Bool})):
  match a b c:
    case True{} True{} True{}:
      ({==}, ({==}, {==}))
    case True{} True{} False{}:
      Empty.absurd(
        Merge.And({True{} == True{}: Bool}, Merge.And({True{} == True{}: Bool}, {False{} == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )
    case True{} False{} z:
      Empty.absurd(
        Merge.And({True{} == True{}: Bool}, Merge.And({False{} == True{}: Bool}, {z == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )
    case False{} y z:
      Empty.absurd(
        Merge.And({False{} == True{}: Bool}, Merge.And({y == True{}: Bool}, {z == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )

# the work that a merge that gives an act is of
def Merge.act_acted(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  e: {Merge.act.go(~d, l, k, hb, ho, ht, True{}, md) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Acted(
  ~d,
  Merge.all(~d, l, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, md, []), Some{Work{l, ho, []}}),
  h2,
  ns
):
  Merge.work_act(
    ~d,
    Merge.all(~d, l, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, md, []), Some{Work{l, ho, []}}),
    vs,
    h2,
    ns,
    e
  )
# a test that gives False when its negation does is true
def Merge.not_false(a: Bool, h: {Bool.not(a) == False{}: Bool}) -> {a == True{}: Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))

# a key that is not among the keys of a difference reads the same in both trees
def Merge.diff_same(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  ks: List<&2, List<&2, U32>>,
  +mo: Maybe<&2, List<&2, U32>>,
  +mt: Maybe<&2, List<&2, U32>>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)) == False{}: Bool},
  eo: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n)) == Some{mo}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  et: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)) == Some{mt}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {mo == mt: Maybe<&2, List<&2, U32>>}:
  Equal.trans(
    Maybe<&2, List<&2, U32>>,
    mo,
    Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
    mt,
    Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
      mo,
      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n)), mo, eo)
    ),
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n))),
      mt,
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
      )(
        Merge.not_false(
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
            Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
          ),
          Equal.trans(
            Bool,
            Bool.not(
              Shared.Maybe.is_eq(
                ~List<&2, U32>,
                ~Shared.List.is_eq(~U32, ~U32.is_eq),
                Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
              )
            ),
            List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)),
            False{},
            Equal.sym(
              Bool,
              List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)),
              Bool.not(
                Shared.Maybe.is_eq(
                  ~List<&2, U32>,
                  ~Shared.List.is_eq(~U32, ~U32.is_eq),
                  Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                  Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
                )
              ),
              Merge.laws_diff(d)(l)(ho)(ht)(ks)(ediff)(Vend.Key.res(n))
            ),
            ec
          )
        )
      ),
      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)), mt, et)
    )
  )
# a merge whose keys do not name a resource, which reads the same in both
# trees, leaves it, and its merge takes a side, so it is that side
def Merge.takes_core.fo(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)) == False{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o),
  ft: Merge.Found(~d, l, ht, n, th)
) -> {Vend.Res.find(~d, lf, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  (+mt, r2) = ft
  (+et1, +et2) = r2
  %Equal.sym(
    Maybe<&2, Requests.Res>,
    x,
    o,
    Merge.take_value(
      ~d,
      l,
      b,
      o,
      th,
      x,
      hp,
      Equal.trans(
        Maybe<&2, Requests.Res>,
        o,
        Vend.Res.found(mo),
        th,
        Equal.sym(Maybe<&2, Requests.Res>, Vend.Res.found(mo), o, eo2),
        Equal.trans(
          Maybe<&2, Requests.Res>,
          Vend.Res.found(mo),
          Vend.Res.found(mt),
          th,
          Equal.cong(
            Maybe<&2, List<&2, U32>>,
            Maybe<&2, Requests.Res>,
            v => Vend.Res.found(v),
            mo,
            mt,
            Merge.diff_same(~d, l, ho, ht, n, ks, mo, mt, ediff, ec, eo1, et1)
          ),
          et2
        )
      )
    )
  ): {Vend.Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
  %eo2: {Vend.Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
  Merge.find_res(
    ~d,
    lf,
    hf,
    n,
    mo,
    Merge.all_frame(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      n,
      mo,
      ks,
      l,
      ho,
      [],
      lf,
      hf,
      N,
      eall,
      {==},
      wf,
      held,
      ec,
      Replicas.Hist.find(
        ~Requests.Ask.machine(),
        ~d,
        l,
        lf,
        ho,
        Vend.Key.res(n),
        mo,
        Merge.grows_of(~d, l, l, lf, [], N, {==}, wf, nd)
      )(eo1)
    )
  )

# a merge whose pick of a resource takes a side reads the resource as that side
def Merge.takes_core.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +c: Bool,
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)) == c: Bool}
) -> {Vend.Res.find(~d, lf, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  match c:
    case True{}:
      %Merge.found_value(x): {Vend.Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
      Merge.find_res(
        ~d,
        lf,
        hf,
        n,
        Vend.Res.value(x),
        Merge.all_take(~d, l, hb, ho, ht, k, n, b, o, th, x, ks, l, ho, [], lf, hf, N, eall, {==}, wf, held, hb0, ho0, ht0, hp, ec)
      )
    case False{}:
      Merge.takes_core.fo(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        x,
        ks,
        lf,
        hf,
        N,
        eall,
        wf,
        held,
        nd,
        hp,
        ediff,
        ec,
        Merge.find_some(~d, l, ho, n, o, ho0),
        Merge.find_some(~d, l, ht, n, th, ht0)
      )

# the merge of a resource whose pick takes a side, as the work that the merge
# ends in, is that side in the ledger of its nodes
def Merge.takes_final(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<Vend.L(d)>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<Vend.L(d)>>},
  +eroot: {Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>},
  +enodes: {Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>},
  +held: Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  match W:
    case Work{+lf, +hf, +N}:
      %enodes: {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      %eroot: {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      %Merge.And.left(
        Merge.Puts(~d, l, lf, N),
        Merge.Nodes([], N),
        Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
      ): {Vend.Res.find(~d, _, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      Merge.takes_core.at(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        x,
        ks,
        lf,
        hf,
        N,
        eall,
        Merge.And.left(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        hb0,
        ho0,
        ht0,
        hp,
        ediff,
        List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)),
        {==}
      )
# the keys that a merge goes through are those of the difference
def Merge.keys_def(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ks: List<&2, List<&2, U32>>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> {
  Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []) == ks: List<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, List<&2, List<&2, U32>>>,
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
    Some{ks},
    ediff
  ): {Maybe.default(&2, List<&2, List<&2, U32>>, _, []) == ks: List<&2, List<&2, U32>>}
  {==}

# what a merge that gives an act has gone through: from the keys of the
# difference ks, the work W that it ends in, whose root is h2 and whose nodes
# are ns
def Merge.Facts.work(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<Vend.L(d)>
) -> Data:
  Merge.And({Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<Vend.L(d)>>}, Merge.And({Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>}, Merge.And({Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>}, Merge.And({Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}, Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W))))))

# what a merge that gives an act has gone through
def Merge.Facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>
) -> Data:
  Sigma<&2, &2, List<&2, List<&2, U32>>, ks => Sigma<&2, &2, Work<Vend.L(d)>, W => Merge.Facts.work(~d, l, hb, ho, ht, k, h2, ns, ks, W)>>

# what a merge has gone through, once the act of the merge is known to be of a
# work
def Merge.facts_acted(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +ks: List<&2, List<&2, U32>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  ),
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  (+W, st) = acted
  (+eall0, st2) = st
  (+eroot, st3) = st2
  (+enodes, held) = st3
  (
    ks,
    (
      W,
      (
        %Merge.keys_def(~d, l, ho, ht, ks, ediff): {
          Merge.all(~d, l, hb, ho, ht, k, _, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<Vend.L(d)>>
        }
        eall0,
        (eroot, (enodes, (ediff, held)))
      )
    )
  )

# the bindings that a tree lists whole
def Merge.Listed(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>) -> Data:
  Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>

# what a merge has gone through, once the difference of the trees is known to be
# there (md)
def Merge.facts_ks(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  +emd: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == md: Maybe<&2, List<&2, List<&2, U32>>>},
  hs: {Maybe.is_some(&2, List<&2, List<&2, U32>>, md) == True{}: Bool},
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  )
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  match md:
    case None{}:
      Empty.absurd(Merge.Facts(~d, l, hb, ho, ht, k, h2, ns), Shared.Bool.false_ne_true(hs))
    case Some{+ks}:
      Merge.facts_acted(~d, l, hb, ho, ht, k, ks, h2, ns, acted, emd)

# what a merge has gone through, once the two trees are known to list whole
def Merge.facts_r2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  r1: Merge.Listed(~d, l, ho),
  r2: Merge.Listed(~d, l, ht),
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  )
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  (+bs1, e1) = r1
  (+bs2, e2) = r2
  Merge.facts_ks(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    h2,
    ns,
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
    {==},
    Merge.whole_diff(
      Vend.L(d),
      Replicas.Led.tree(Requests.Ask.machine(), d),
      Merge.laws_whole(d),
      l,
      ho,
      ht,
      bs1,
      bs2,
      e1,
      e2
    ),
    acted
  )

# the act of a merge is the act once its trees are checked
def Merge.act_go_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> {
  Merge.act.go(
    ~d,
    l,
    k,
    Base.tree(base),
    Replicas.Tip.content(t),
    Vend.Source.root(from),
    Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from))
  )
    == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
}:
  Equal.trans(
    Maybe<&2, Replicas.Act>,
    Merge.act.go(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Vend.Source.root(from),
      Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from))
    ),
    Merge.act(~d, l, t, k, from, base),
    Some{Replicas.Act.Taken{vs, h2, ns}},
    Equal.sym(
      Maybe<&2, Replicas.Act>,
      Merge.act(~d, l, t, k, from, base),
      Merge.act.go(
        ~d,
        l,
        k,
        Base.tree(base),
        Replicas.Tip.content(t),
        Vend.Source.root(from),
        Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from))
      ),
      Merge.act_eq(~d, l, t, k, from, base)
    ),
    e0
  )

# what a merge that gives an act has gone through
def Merge.facts_go(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Facts(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from), k, h2, ns):
  Merge.facts_r2(
    ~d,
    l,
    Base.tree(base),
    Replicas.Tip.content(t),
    Vend.Source.root(from),
    k,
    h2,
    ns,
    Merge.kept_range(
      ~d,
      l,
      Replicas.Tip.content(t),
      Merge.And.right(
        {Vend.Tree.kept(~d, l, Base.tree(base)) == True{}: Bool},
        {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
        Merge.And.right(
          {Vend.Tree.kept(~d, l, Vend.Source.root(from)) == True{}: Bool},
          Merge.And({Vend.Tree.kept(~d, l, Base.tree(base)) == True{}: Bool}, {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}),
          Merge.guard3(
            Vend.Tree.kept(~d, l, Vend.Source.root(from)),
            Vend.Tree.kept(~d, l, Base.tree(base)),
            Vend.Tree.kept(~d, l, Replicas.Tip.content(t)),
            Merge.act_ok(
              ~d,
              l,
              k,
              Base.tree(base),
              Replicas.Tip.content(t),
              Vend.Source.root(from),
              Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
              Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
              Replicas.Act.Taken{vs, h2, ns},
              Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
            )
          )
        )
      )
    ),
    Merge.kept_range(
      ~d,
      l,
      Vend.Source.root(from),
      Merge.And.left(
        {Vend.Tree.kept(~d, l, Vend.Source.root(from)) == True{}: Bool},
        Merge.And({Vend.Tree.kept(~d, l, Base.tree(base)) == True{}: Bool}, {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}),
        Merge.guard3(
          Vend.Tree.kept(~d, l, Vend.Source.root(from)),
          Vend.Tree.kept(~d, l, Base.tree(base)),
          Vend.Tree.kept(~d, l, Replicas.Tip.content(t)),
          Merge.act_ok(
            ~d,
            l,
            k,
            Base.tree(base),
            Replicas.Tip.content(t),
            Vend.Source.root(from),
            Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
            Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
            Replicas.Act.Taken{vs, h2, ns},
            Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
          )
        )
      )
    ),
    Merge.act_acted(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Vend.Source.root(from),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
      vs,
      h2,
      ns,
      %Merge.act_ok(
        ~d,
        l,
        k,
        Base.tree(base),
        Replicas.Tip.content(t),
        Vend.Source.root(from),
        Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
        Replicas.Act.Taken{vs, h2, ns},
        Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
      ): {
        Merge.act.go(
          ~d,
          l,
          k,
          Base.tree(base),
          Replicas.Tip.content(t),
          Vend.Source.root(from),
          _,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from))
        )
          == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
      }
      Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
    )
  )

# a merge whose pick of a resource takes a side, once it is known what it has
# gone through, gives a tree that reads the resource as that side
def Merge.takes_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  fs: Merge.Facts(~d, l, hb, ho, ht, k, h2, ns),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>}
) -> {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  (+ks, r1) = fs
  (+W, r2) = r1
  (+eall, r3) = r2
  (+eroot, r4) = r3
  (+enodes, r5) = r4
  (+ediff, held) = r5
  Merge.takes_final(~d, l, hb, ho, ht, k, n, b, o, th, x, ks, W, h2, ns, eall, eroot, enodes, held, hb0, ho0, ht0, hp, ediff)

# a merge that gives an act, and whose pick of a resource takes a side, gives a
# tree that reads the resource as that side
def Merge.takes_go(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>},
  +hb0: {Vend.Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, Vend.Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>}
) -> {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  Merge.takes_facts(
    ~d,
    l,
    Base.tree(base),
    Replicas.Tip.content(t),
    Vend.Source.root(from),
    k,
    h2,
    ns,
    n,
    b,
    o,
    th,
    x,
    Merge.facts_go(~d, l, t, k, from, base, vs, h2, ns, e0),
    hb0,
    ho0,
    ht0,
    hp
  )

# the pick of the merge of a resource, as the premises say, gave the work W1
def Merge.one_pick(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  hb0: {mb == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +q: Pick,
  hq: {Pick.merge(~d, l, b0, o0, t0) == Some{q}: Maybe<&2, Pick>}
) -> {Merge.pick(~d, Work{lc, hc, P}, k, n, q) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  %Merge.pick_same(
    ~d,
    l,
    b,
    o,
    t,
    b0,
    o0,
    t0,
    p,
    q,
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      b,
      b0,
      Equal.trans(Maybe<&2, Maybe<&2, Requests.Res>>, Some{b}, mb, Some{b0}, Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, mb, Some{b}, eb), hb0)
    ),
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      o,
      o0,
      Equal.trans(
        Maybe<&2, Maybe<&2, Requests.Res>>,
        Some{o},
        Vend.Res.find(~d, l, ho, n),
        Some{o0},
        Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Vend.Res.find(~d, l, ho, n), Some{o}, eo),
        ho0
      )
    ),
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      t,
      t0,
      Equal.trans(
        Maybe<&2, Maybe<&2, Requests.Res>>,
        Some{t},
        Vend.Res.find(~d, l, ht, n),
        Some{t0},
        Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Vend.Res.find(~d, l, ht, n), Some{t}, et),
        ht0
      )
    ),
    ep,
    hq
  ): {Merge.pick(~d, Work{lc, hc, P}, k, n, _) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
  e

# the tree of the work after the next merge of the resource n, whose pick
# clashes, reads the key of the resource as it did
def Merge.next_clash_frame(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  Merge.pick_frame.clash.at(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    n,
    W1,
    lf,
    N,
    Vend.Clash.names(~d, lc, hc, k),
    Merge.one_pick(
      ~d,
      l,
      lc,
      ho,
      ht,
      hc,
      P,
      k,
      n,
      b0,
      o0,
      t0,
      Vend.Res.find(~d, l, hb, n),
      W1,
      Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
      hb0,
      ho0,
      ht0,
      Pick.Clash{},
      hpc
    ),
    wc,
    wf,
    held,
    nd,
    v,
    kn
  )
# the last of three that or to false is false
def Merge.or_last(
  a: Bool,
  b: Bool,
  c: Bool,
  h: {Bool.or(a, Bool.or(b, c)) == False{}: Bool}
) -> {c == False{}: Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Bool.or(a, True{}),
            False{},
            Equal.sym(Bool, Bool.or(a, True{}), True{}, Shared.Bool.or_true_right(a)),
            %Shared.Bool.or_true_right(b): {Bool.or(a, _) == False{}: Bool}
            h
          )
        )
      )

# a test is false, when it is not true
def Merge.false_of(q: Bool, h: {q == True{}: Bool} -> Empty) -> {q == False{}: Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{}: Bool}, h({==}))

# whether a pick clashes
def Merge.is_clash(p: Pick) -> Bool:
  match p:
    case Pick.Clash{}:
      True{}
    case _:
      False{}

# a merge that clashes, once the side that it takes is known (s), is a merge of
# two sides that differ
def Merge.clash_diff.at(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  s: Sides.Side,
  es: {Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th) == s: Sides.Side},
  hp: {Pick.side(~d, l, b, o, th, s) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {Vend.Res.same(o, th) == False{}: Bool}:
  match s:
    case Sides.Side.Theirs{}:
      Empty.absurd(
        {Vend.Res.same(o, th) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Pick,
            Bool,
            q => Merge.is_clash(q),
            Pick.Take{th},
            Pick.Clash{},
            Shared.Maybe.some_inj(Pick, Pick.Take{th}, Pick.Clash{}, hp)
          )
        )
      )
    case Sides.Side.Ours{}:
      Empty.absurd(
        {Vend.Res.same(o, th) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Pick,
            Bool,
            q => Merge.is_clash(q),
            Pick.Take{o},
            Pick.Clash{},
            Shared.Maybe.some_inj(Pick, Pick.Take{o}, Pick.Clash{}, hp)
          )
        )
      )
    case Sides.Side.Both{}:
      Merge.or_last(
        Vend.Res.same(o, b),
        Vend.Res.same(th, b),
        Vend.Res.same(o, th),
        Sides.Side.both_changed(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th)(es)
      )

# a merge that clashes is a merge of two sides that differ
def Merge.clash_diff(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {Vend.Res.same(o, th) == False{}: Bool}:
  Merge.clash_diff.at(~d, l, b, o, th, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, th), {==}, hp)

# two reads of the same resource that differ in the keys of a difference are in
# the keys that the difference lists
def Merge.clash_in_diff(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  ks: List<&2, List<&2, U32>>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  cd: {Vend.Res.same(o, th) == False{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o),
  ft: Merge.Found(~d, l, ht, n, th)
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)) == True{}: Bool}:
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  (+mt, r2) = ft
  (+et1, +et2) = r2
  Equal.trans(
    Bool,
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)),
    Bool.not(
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
      )
    ),
    True{},
    Merge.laws_diff(d)(l)(ho)(ht)(ks)(ediff)(Vend.Key.res(n)),
    Equal.cong(
      Bool,
      Bool,
      q => Bool.not(q),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
      ),
      False{},
      Merge.false_of(
        Shared.Maybe.is_eq(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
          Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
        ),
        hq => Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Vend.Res.same(o, th),
            True{},
            Equal.sym(Bool, Vend.Res.same(o, th), False{}, cd),
            %Equal.trans(
              Maybe<&2, Requests.Res>,
              o,
              Vend.Res.found(mo),
              th,
              Equal.sym(Maybe<&2, Requests.Res>, Vend.Res.found(mo), o, eo2),
              Equal.trans(
                Maybe<&2, Requests.Res>,
                Vend.Res.found(mo),
                Vend.Res.found(mt),
                th,
                Equal.cong(
                  Maybe<&2, List<&2, U32>>,
                  Maybe<&2, Requests.Res>,
                  v => Vend.Res.found(v),
                  mo,
                  mt,
                  Equal.trans(
                    Maybe<&2, List<&2, U32>>,
                    mo,
                    Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                    mt,
                    Equal.sym(
                      Maybe<&2, List<&2, U32>>,
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                      mo,
                      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n)), mo, eo1)
                    ),
                    Equal.trans(
                      Maybe<&2, List<&2, U32>>,
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n))),
                      mt,
                      Shared.Maybe.is_eq_sound(
                        ~List<&2, U32>,
                        ~Shared.List.is_eq(~U32, ~U32.is_eq),
                        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
                        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Vend.Key.res(n))),
                        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)))
                      )(hq),
                      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Vend.Key.res(n)), mt, et1)
                    )
                  )
                ),
                et2
              )
            ): {Vend.Res.same(o, _) == True{}: Bool}
            Merge.same_refl(o)
          )
        )
      )
    )
  )
# the resources that a read of the key of the open clashes tells are open (the
# body of Clash.names, apart from the read)
def Merge.names_of(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(
    &2,
    Maybe<&2, List<&2, Resources.Name>>,
    List<&2, Resources.Name>,
    x => Maybe.default(&2, List<&2, Resources.Name>, x, []),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      m
    )
  )

# the clash of the resource n is among the resources that mc tells (the body of
# Clash.open, apart from the clashes)
def Merge.open_of(n: Resources.Name, mc: Maybe<&2, List<&2, Resources.Name>>) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    mc
  )

# the clashes that are open in the tree h of l are cs, and n is among them
def Merge.Names(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>, k: Ledgers.Id, n: Resources.Name) -> Data:
  Sigma<&2, &2, List<&2, Resources.Name>, cs => Merge.And({Vend.Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}, {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool})>

# a read of the key K of the tree h of l is known as the value v
def Merge.Known(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>, K: List<&2, U32>) -> Data:
  Sigma<&2, &2, Maybe<&2, List<&2, U32>>, v => {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, K) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}>

# a clash that is open, once the clashes that are open are read (mc), gives the
# clashes that are open and a name among them
def Merge.open_names.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Vend.Clash.names(~d, l, h, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  e: {Merge.open_of(n, mc) == Some{True{}}: Maybe<&2, Bool>}
) -> Merge.Names(~d, l, h, k, n):
  match mc:
    case None{}:
      Empty.absurd(Merge.Names(~d, l, h, k, n), Shared.Maybe.none_ne_some(Bool, True{}, e))
    case Some{+cs}:
      (cs, (emc, Shared.Maybe.some_inj(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, e)))

# a clash that is open is among the clashes that are open
def Merge.open_names(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  e: {Vend.Clash.open(~d, l, h, n, k) == Some{True{}}: Maybe<&2, Bool>}
) -> Merge.Names(~d, l, h, k, n):
  Merge.open_names.at(~d, l, h, k, n, Vend.Clash.names(~d, l, h, k), {==}, e)

# a resource among the clashes that are open has its clash open
def Merge.names_open(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  ns: Merge.Names(~d, l, h, k, n)
) -> {Vend.Clash.open(~d, l, h, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = ns
  (ec, ct) = r
  %Equal.sym(Maybe<&2, List<&2, Resources.Name>>, Vend.Clash.names(~d, l, h, k), Some{cs}, ec): {
    Merge.open_of(n, _) == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, ct): {
    Some{_} == Some{True{}}: Maybe<&2, Bool>
  }
  {==}

# the clashes that are open, once the read of them is known (m), give a value
# that the read finds
def Merge.names_known.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.clashes(k)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {Merge.names_of(m) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> Merge.Known(~d, l, h, Vend.Key.clashes(k)):
  match m:
    case None{}:
      Empty.absurd(Merge.Known(~d, l, h, Vend.Key.clashes(k)), Shared.Maybe.none_ne_some(List<&2, Resources.Name>, cs, e))
    case Some{+v}:
      (v, em)

# the clashes that are open are read as a value
def Merge.names_known(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  e: {Vend.Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> Merge.Known(~d, l, h, Vend.Key.clashes(k)):
  Merge.names_known.at(~d, l, h, k, cs, Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.clashes(k)), {==}, e)

# the clashes that are open stay the same as the ledger grows
def Merge.names_grows.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Vend.Key.clashes(k)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  e: {Merge.names_of(m) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Vend.Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  match m:
    case None{}:
      Empty.absurd(
        {Vend.Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>},
        Shared.Maybe.none_ne_some(List<&2, Resources.Name>, cs, e)
      )
    case Some{+v}:
      %Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, h, Vend.Key.clashes(k)),
        Some{v},
        Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, h, Vend.Key.clashes(k), v, g)(em)
      ): {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
      e

# the clashes that are open in a ledger are open in a ledger that grows from it
def Merge.names_grows(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  e: {Vend.Clash.names(~d, a, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Vend.Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  Merge.names_grows.at(~d, a, b, h, k, cs, Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Vend.Key.clashes(k)), {==}, g, e)

# two trees that read the key of the open clashes alike have the same clashes
# that are open
def Merge.names_same(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  v: Maybe<&2, List<&2, U32>>,
  kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.clashes(k)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  kn1: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h1, Vend.Key.clashes(k)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {Vend.Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Vend.Clash.names(~d, l, h1, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h1, Vend.Key.clashes(k)),
    Some{v},
    kn1
  ): {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
  %kn: {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
  e

# the clashes that a read of the code of some resources tells are those
# resources
def Merge.names_of_value(
  +y: Resources.Name,
  +ys: List<&2, Resources.Name>
) -> {Merge.names_of(Some{Vend.Clash.value(y <> ys)}) == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(
    Maybe<&2, List<&2, Resources.Name>>,
    Codes.Code.whole.read(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Codes.Code.list(~Resources.Name, ~Resources.Name.code, y <> ys, [])
    ),
    Some{y <> ys},
    Codes.Code.whole_read(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      ~(xs => r => Codes.Code.list_read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, ~(a => s => Resources.Name.code_read(a, s)), xs, r)),
      y <> ys
    )
  ): {Some{Maybe.default(&2, List<&2, Resources.Name>, _, [])} == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}
  {==}
# the clashes among which a resource is put, when it is among them, are the same
def Merge.put_true(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {Vend.Clash.put(n, cs) == cs: List<&2, Resources.Name>}:
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, ep): {
    Shared.Bool.when(List<&2, Resources.Name>, _, u => cs, u => n <> cs) == cs: List<&2, Resources.Name>
  }
  {==}

# the clashes among which a resource is put, when it is not among them, are
# those and it
def Merge.put_false(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == False{}: Bool}
) -> {Vend.Clash.put(n, cs) == n <> cs: List<&2, Resources.Name>}:
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), False{}, ep): {
    Shared.Bool.when(List<&2, Resources.Name>, _, u => cs, u => n <> cs) == n <> cs: List<&2, Resources.Name>
  }
  {==}

# the clashes are some, and others
def Merge.Cons(-ps: List<&2, Resources.Name>) -> Data:
  Sigma<&2, &2, Resources.Name, y => Sigma<&2, &2, List<&2, Resources.Name>, ys => {ps == y <> ys: List<&2, Resources.Name>}>>

# the clashes among which a resource is put are some, once it is known whether
# it is among them (p)
def Merge.put_cons.at(
  p: Bool,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == p: Bool}
) -> Merge.Cons(Vend.Clash.put(n, cs)):
  match p:
    case False{}:
      (n, (cs, Merge.put_false(n, cs, ep)))
    case True{}:
      match cs:
        case Nil{}:
          Empty.absurd(Merge.Cons(Vend.Clash.put(n, [])), Shared.Bool.false_ne_true(ep))
        case Con{+y, +ys}:
          (y, (ys, Merge.put_true(n, y <> ys, ep)))

# the clashes among which a resource is put are some
def Merge.put_cons(+n: Resources.Name, +cs: List<&2, Resources.Name>) -> Merge.Cons(Vend.Clash.put(n, cs)):
  Merge.put_cons.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), n, cs, {==})

# a resource that is put among the clashes is among them, once it is known
# whether it was among them (p)
def Merge.put_self.at(
  p: Bool,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  +ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == p: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Vend.Clash.put(n, cs), n) == True{}: Bool}:
  match p:
    case True{}:
      %Equal.sym(List<&2, Resources.Name>, Vend.Clash.put(n, cs), cs, Merge.put_true(n, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      ep
    case False{}:
      %Equal.sym(List<&2, Resources.Name>, Vend.Clash.put(n, cs), n <> cs, Merge.put_false(n, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      %Equal.sym(Bool, Resources.Name.is_eq(n, n), True{}, Resources.Name.is_eq_refl(n)): {
        List.any.if(u => List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), _) == True{}: Bool
      }
      {==}

# a resource that is put among the clashes is among them
def Merge.put_self(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Vend.Clash.put(n, cs), n) == True{}: Bool}:
  Merge.put_self.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), n, cs, {==})

# a resource that is put among the clashes keeps those that were among them,
# once it is known whether it was among them (p)
def Merge.put_keep.at(
  p: Bool,
  +n1: Resources.Name,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n1) == p: Bool},
  h: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Vend.Clash.put(n1, cs), n) == True{}: Bool}:
  match p:
    case True{}:
      %Equal.sym(List<&2, Resources.Name>, Vend.Clash.put(n1, cs), cs, Merge.put_true(n1, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      h
    case False{}:
      %Equal.sym(List<&2, Resources.Name>, Vend.Clash.put(n1, cs), n1 <> cs, Merge.put_false(n1, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      Shared.List.contains_cons(~Resources.Name, ~Resources.Name.is_eq, n1, cs, n)(h)

# a resource that is put among the clashes keeps those that were among them
def Merge.put_keep(
  +n1: Resources.Name,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  h: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Vend.Clash.put(n1, cs), n) == True{}: Bool}:
  Merge.put_keep.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n1), n1, n, cs, {==}, h)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of some clashes, are those
def Merge.names_value(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  ps: List<&2, Resources.Name>,
  +y: Resources.Name,
  +ys: List<&2, Resources.Name>,
  +ec: {ps == y <> ys: List<&2, Resources.Name>},
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)) == Trees.Look.of(Vend.Clash.value(ps)): Trees.Look}
) -> {Vend.Clash.names(~d, lf, h1, k) == Some{ps}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(List<&2, Resources.Name>, ps, y <> ys, ec): {Vend.Clash.names(~d, lf, h1, k) == Some{_}: Maybe<&2, List<&2, Resources.Name>>}
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)),
    Some{Vend.Clash.value(y <> ys)},
    Merge.known_of(
      Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)),
      Vend.Clash.value(y <> ys),
      %ec: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)) == Trees.Look.of(Vend.Clash.value(_)): Trees.Look}
      e
    )
  ): {Merge.names_of(_) == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}
  Merge.names_of_value(y, ys)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of the clashes among which a resource is put, are those, once they
# are known to be some (cn)
def Merge.names_put.at(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  cn: Merge.Cons(Vend.Clash.put(n, cs)),
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)) == Trees.Look.of(Vend.Clash.value(Vend.Clash.put(n, cs))): Trees.Look}
) -> {Vend.Clash.names(~d, lf, h1, k) == Some{Vend.Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>}:
  (+y, r) = cn
  (+ys, ec) = r
  Merge.names_value(~d, lf, h1, k, Vend.Clash.put(n, cs), y, ys, ec, e)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of the clashes among which a resource is put, are those
def Merge.names_put(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Vend.Key.clashes(k)) == Trees.Look.of(Vend.Clash.value(Vend.Clash.put(n, cs))): Trees.Look}
) -> {Vend.Clash.names(~d, lf, h1, k) == Some{Vend.Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>}:
  Merge.names_put.at(~d, lf, h1, k, n, cs, Merge.put_cons(n, cs), e)

# the clashes that are open before a clash, in the ledger of its nodes, and
# those after it, with the resource put among them
def Merge.Clashed(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  hc: Maybe<&2, Hashes.Hash>,
  h1: Maybe<&2, Hashes.Hash>,
  k: Ledgers.Id,
  n: Resources.Name
) -> Data:
  Sigma<&2, &2, List<&2, Resources.Name>, cs => Merge.And({Vend.Clash.names(~d, lf, hc, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}, {Vend.Clash.names(~d, lf, h1, k) == Some{Vend.Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>})>

# what a clash does to the clashes that are open, once the ones that were open
# are read (mc)
def Merge.clash_after(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Vend.Clash.names(~d, lc, hc, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<Vend.L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<Vend.L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Clashed(~d, lf, hc, Merge.root(~d, W1), k, n):
  match mc:
    case None{}:
      Empty.absurd(Merge.Clashed(~d, lf, hc, Merge.root(~d, W1), k, n), Shared.Maybe.none_ne_some(Work<Vend.L(d)>, W1, eb))
    case Some{+cs}:
      (
        cs,
        (
          Merge.names_grows(
            ~d,
            lc,
            lf,
            hc,
            k,
            cs,
            Merge.grows_of(
              ~d,
              l,
              lc,
              lf,
              P,
              N,
              wc,
              wf,
              Merge.nodes_trans(
                P,
                Merge.nodes(~d, W1),
                N,
                Merge.And.right(
                  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
                  Merge.Nodes(P, Merge.nodes(~d, W1)),
                  Merge.set_facts(~d, l, lc, hc, P, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)), W1, eb, wc)
                ),
                nd
              )
            ),
            emc
          ),
          Merge.names_put(
            ~d,
            lf,
            Merge.root(~d, W1),
            k,
            n,
            cs,
            Merge.writes_hit(
              ~d,
              lf,
              Merge.root(~d, W1),
              hc,
              Vend.Key.clashes(k),
              Vend.Clash.value(Vend.Clash.put(n, cs)),
              Merge.set_core(
                ~d,
                l,
                lc,
                hc,
                P,
                Vend.Key.clashes(k),
                Vend.Clash.value(Vend.Clash.put(n, cs)),
                lf,
                N,
                W1,
                Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs))),
                {==},
                eb,
                wc,
                wf,
                held,
                nd
              )
            )
          )
        )
      )

# the clash of a resource that a clash opens is open, once the clashes are known
# (cl)
def Merge.hit_of(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  cl: Merge.Clashed(~d, lf, hc, h1, k, n)
) -> {Vend.Clash.open(~d, lf, h1, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = cl
  (nb, na) = r
  Merge.names_open(~d, lf, h1, k, n, (Vend.Clash.put(n, cs), (na, Merge.put_self(n, cs))))

# a pick that clashes opens the clash of its resource
def Merge.clash_hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Clash{}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {Vend.Clash.open(~d, lf, Merge.root(~d, W1), n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.hit_of(
    ~d,
    lf,
    hc,
    Merge.root(~d, W1),
    k,
    n,
    Merge.clash_after(~d, l, lc, hc, P, k, n, W1, lf, N, Vend.Clash.names(~d, lc, hc, k), {==}, e1, wc, wf, held, nd)
  )

# a write of a key that is not the key of the open clashes keeps the clash that
# is open, once the clashes that are open are read as a value (kk)
def Merge.keep_known(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Vend.Key.clashes(k)) == False{}: Bool},
  +cs: List<&2, Resources.Name>,
  +ec: {Vend.Clash.names(~d, lf, hc, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>},
  ct: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n0) == True{}: Bool},
  kk: Merge.Known(~d, lf, hc, Vend.Key.clashes(k))
) -> {Vend.Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+v, +kn) = kk
  Merge.names_open(
    ~d,
    lf,
    h1,
    k,
    n0,
    (
      cs,
      (
        Merge.names_same(~d, lf, hc, h1, k, cs, v, kn, Merge.writes_frame(~d, lf, h1, hc, kw, m, wr, Vend.Key.clashes(k), v, hk, kn), ec),
        ct
      )
    )
  )

# a write of a key that is not the key of the open clashes keeps the clash that
# is open, once the clashes that are open are known (ns)
def Merge.keep_names(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Vend.Key.clashes(k)) == False{}: Bool},
  ns: Merge.Names(~d, lf, hc, k, n0)
) -> {Vend.Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = ns
  (+ec, ct) = r
  Merge.keep_known(~d, lf, hc, h1, k, n0, kw, m, wr, hk, cs, ec, ct, Merge.names_known(~d, lf, hc, k, cs, ec))

# a write of a key that is not the key of the open clashes keeps the clash that
# is open
def Merge.keep_by_writes(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Vend.Key.clashes(k)) == False{}: Bool},
  op: {Vend.Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Vend.Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.keep_names(~d, lf, hc, h1, k, n0, kw, m, wr, hk, Merge.open_names(~d, lf, hc, k, n0, op))

# a clash keeps the clash that is open, once the clashes that are open (ns) and
# the clashes after it (cl) are known
def Merge.keep_clash(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  ns: Merge.Names(~d, lf, hc, k, n0),
  cl: Merge.Clashed(~d, lf, hc, h1, k, n)
) -> {Vend.Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs0, r0) = ns
  (+ec0, ct0) = r0
  (+cs, r1) = cl
  (nb, na) = r1
  Merge.names_open(
    ~d,
    lf,
    h1,
    k,
    n0,
    (
      Vend.Clash.put(n, cs),
      (
        na,
        Merge.put_keep(
          n,
          n0,
          cs,
          %Equal.sym(
            List<&2, Resources.Name>,
            cs,
            cs0,
            Shared.Maybe.some_inj(
              List<&2, Resources.Name>,
              cs,
              cs0,
              Equal.trans(
                Maybe<&2, List<&2, Resources.Name>>,
                Some{cs},
                Vend.Clash.names(~d, lf, hc, k),
                Some{cs0},
                Equal.sym(Maybe<&2, List<&2, Resources.Name>>, Vend.Clash.names(~d, lf, hc, k), Some{cs}, nb),
                ec0
              )
            )
          ): {List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n0) == True{}: Bool}
          ct0
        )
      )
    )
  )

# what a pick of a merge does to the clash that is open in a tree: it keeps it
def Merge.pick_keep(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  p: Pick,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Vend.Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Vend.Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  match p:
    case Pick.Take{+x}:
      Merge.keep_by_writes(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n0,
        Vend.Key.res(n),
        Vend.Res.value(x),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Vend.Key.res(n),
          Vend.Res.value(x),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Vend.Key.res(n), Vend.Res.value(x)),
          {==},
          e1,
          wc,
          wf,
          held,
          nd
        ),
        {==},
        op
      )
    case Pick.Make{+h, +bytes}:
      Merge.keep_by_writes(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n0,
        Vend.Key.res(n),
        Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
        Merge.set_core(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Vend.Key.res(n),
          Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          lf,
          N,
          W1,
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
            hc,
            Vend.Key.res(n),
            Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}})
          ),
          {==},
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc),
          wf,
          held,
          nd
        ),
        {==},
        op
      )
    case Pick.Clash{}:
      Merge.keep_clash(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n,
        n0,
        Merge.open_names(~d, lf, hc, k, n0, op),
        Merge.clash_after(~d, l, lc, hc, P, k, n, W1, lf, N, Vend.Clash.names(~d, lc, hc, k), {==}, e1, wc, wf, held, nd)
      )
# what a merge of a resource does to the clash that is open in a tree: it keeps
# it
def Merge.one_keep.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<Vend.L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Vend.Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Vend.Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_keep(~d, l, lc, hc, P, k, n, n0, p, W1, lf, N, e, wc, wf, held, nd, op)

# the next merge of the work keeps the clash that is open in its tree
def Merge.next_keep(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Vend.Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Vend.Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<Vend.L(d)>, Work{lc, hc, P}, W1, e): {Vend.Clash.open(~d, lf, Merge.root(~d, _), n0, k) == Some{True{}}: Maybe<&2, Bool>}
      op
    case Some{+n}:
      Merge.one_keep.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        n0,
        Vend.Res.find(~d, l, hb, n),
        W1,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
        lf,
        N,
        wc,
        wf,
        held,
        nd,
        op
      )

# the next merge of the resource n, whose pick clashes, opens its clash
def Merge.next_hit_open(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {Vend.Clash.open(~d, lf, Merge.root(~d, W1), n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.clash_hit(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    W1,
    lf,
    N,
    Merge.one_pick(
      ~d,
      l,
      lc,
      ho,
      ht,
      hc,
      P,
      k,
      n,
      b0,
      o0,
      t0,
      Vend.Res.find(~d, l, hb, n),
      W1,
      Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
      hb0,
      ho0,
      ht0,
      Pick.Clash{},
      hpc
    ),
    wc,
    wf,
    held,
    nd
  )

# one of two
type Merge.Or<-A: Data, -B: Data> is Data:
  Merge.Or.Left{left: A}
  Merge.Or.Right{right: B}

# the clash of the resource n is open in the tree h, or the key of n is in the
# keys rest
def Merge.Open(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id,
  rest: List<&2, List<&2, U32>>
) -> Data:
  Merge.Or<{Vend.Clash.open(~d, lf, h, n, k) == Some{True{}}: Maybe<&2, Bool>}, {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Vend.Key.res(n)) == True{}: Bool}>

# what a merge of the keys rest keeps of the resource n: the tree reads it as v,
# and the clash of n is open, or the keys have a key for n
def Merge.Inv(
  ~d: Vend.Led(),
  lf: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id,
  v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>
) -> Data:
  Merge.And({Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, Merge.Open(~d, lf, h, n, k, rest))

# a key that is in the keys x then rest, and is not x, is in rest
def Merge.cons_true.at(
  p: Bool,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  hp: {p == False{}: Bool},
  h: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K), p) == True{}: Bool
  }
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool}:
  match p:
    case True{}:
      Empty.absurd(
        {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool},
        Shared.Bool.true_ne_false(hp)
      )
    case False{}:
      h

# a key that is in the keys x then rest, and is not x, is in rest
def Merge.cons_true(
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, K) == False{}: Bool},
  h: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, K) == True{}: Bool}
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool}:
  Merge.cons_true.at(Shared.List.is_eq(~U32, ~U32.is_eq, x, K), rest, K, hx, h)

# the merge of the key of the resource n, whose pick clashes, keeps the resource
# as it was, and opens its clash
def Merge.next_inv.hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  (
    Merge.next_clash_frame(~d, l, lc, hb, ho, ht, hc, P, k, n, b0, o0, t0, v, W1, lf, N, e, hb0, ho0, ht0, hpc, wc, wf, held, nd, kn),
    Merge.Or.Left{Merge.next_hit_open(~d, l, lc, hb, ho, ht, hc, P, k, n, b0, o0, t0, W1, lf, N, e, hb0, ho0, ht0, hpc, wc, wf, held, nd)}
  )

# the merge of a key that is not the key of the resource n keeps the resource as
# it was, and the clash that is open or the key, once the one is known (orr)
def Merge.next_inv.or(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n)) == False{}: Bool},
  orr: Merge.Open(~d, lf, hc, n, k, x <> rest)
) -> Merge.Open(~d, lf, Merge.root(~d, W1), n, k, rest):
  match orr:
    case Merge.Or.Left{+opn}:
      Merge.Or.Left{Merge.next_keep(~d, l, lc, hb, ho, ht, hc, P, k, n, Res.name(x), W1, lf, N, e, wc, wf, held, nd, opn)}
    case Merge.Or.Right{+ctn}:
      Merge.Or.Right{Merge.cons_true(x, rest, Vend.Key.res(n), hx, ctn)}

# the merge of a key that is not the key of the resource n keeps the resource as
# it was, and the clash that is open or the key
def Merge.next_inv.miss(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n)) == False{}: Bool},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  (+kn, orr) = inv
  (
    Merge.next_frame(~d, l, lc, hb, ho, ht, hc, P, k, n, Res.name(x), W1, lf, N, e, wc, wf, held, nd, Merge.apart_of(x, n, hx), v, kn),
    Merge.next_inv.or(~d, l, lc, hb, ho, ht, hc, P, k, n, x, rest, W1, lf, N, e, wc, wf, held, nd, hx, orr)
  )

# what the merge of the key x does to the resource n, once it is known whether
# x is its key (p)
def Merge.next_inv.at(
  ~d: Vend.Led(),
  p: Bool,
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n)) == p: Bool},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  match p:
    case True{}:
      (+kn, orr) = inv
      Merge.next_inv.hit(
        ~d,
        l,
        lc,
        hb,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        b0,
        o0,
        t0,
        v,
        rest,
        W1,
        lf,
        N,
        %Merge.name_of_key(x, n, ep): {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, _) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>}
        e,
        hb0,
        ho0,
        ht0,
        hpc,
        wc,
        wf,
        held,
        nd,
        kn
      )
    case False{}:
      Merge.next_inv.miss(~d, l, lc, hb, ho, ht, hc, P, k, n, v, x, rest, W1, lf, N, e, wc, wf, held, nd, ep, inv)

# what the merge of the key x does to the resource n
def Merge.next_inv(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<Vend.L(d)>,
  +lf: Vend.L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  Merge.next_inv.at(
    ~d,
    Shared.List.is_eq(~U32, ~U32.is_eq, x, Vend.Key.res(n)),
    l,
    lc,
    hb,
    ho,
    ht,
    hc,
    P,
    k,
    n,
    b0,
    o0,
    t0,
    v,
    x,
    rest,
    W1,
    lf,
    N,
    e,
    hb0,
    ho0,
    ht0,
    hpc,
    wc,
    wf,
    held,
    nd,
    {==},
    inv
  )
# the induction hypothesis of Merge.all_inv for the keys rest
def Merge.InvIH(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>,
  lf: Vend.L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: Vend.L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> Merge.Inv(~d, lf, hc1, n, k, v, rest) -> Merge.Inv(~d, lf, hf, n, k, v, [])

# Merge.all_inv for the keys x then rest, once the work W1 after the first step
# is known
def Merge.all_inv.con2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest),
  W1: Work<Vend.L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<Vend.L(d)>>},
  ih: Merge.InvIH(~d, l, hb, ho, ht, k, n, v, rest, lf, hf, N)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  match W1:
    case Work{+lc1, +hc1, +P1}:
      ih(lc1)(hc1)(P1)(erest)(
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
        )
      )(
        Merge.next_inv(
          ~d,
          l,
          lc,
          hb,
          ho,
          ht,
          hc,
          P,
          k,
          n,
          b0,
          o0,
          t0,
          v,
          x,
          rest,
          Work{lc1, hc1, P1},
          lf,
          N,
          enext,
          hb0,
          ho0,
          ht0,
          hpc,
          wc,
          wf,
          held,
          Merge.And.right(
            Merge.Puts(~d, l, lf, N),
            Merge.Nodes(P1, N),
            Merge.all_puts(
              ~d,
              l,
              hb,
              ho,
              ht,
              k,
              rest,
              lc1,
              hc1,
              P1,
              lf,
              hf,
              N,
              erest,
              Merge.And.left(
                Merge.Puts(~d, l, lc1, P1),
                Merge.Nodes(P, P1),
                Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
              )
            )
          ),
          inv
        )
      )

# Merge.all_inv for the keys x then rest, once the first step is known
def Merge.all_inv.con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest),
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.InvIH(~d, l, hb, ho, ht, k, n, v, rest, lf, hf, N)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_inv.con2(~d, l, hb, ho, ht, k, n, b0, o0, t0, v, x, rest, lc, hc, P, lf, hf, N, wc, wf, held, hb0, ho0, ht0, hpc, inv, W1, erest, enext, ih)

# a merge of keys, among which is the key of a resource whose pick clashes, keeps
# the resource as it was, and opens its clash
def Merge.all_inv(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  xs: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, xs)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  match xs:
    case Nil{}:
      %Merge.work_eq.root(~d, lc, hc, P, lf, hf, N, e): Merge.Inv(~d, lf, _, n, k, v, [])
      inv
    case Con{+x, +rest}:
      Merge.all_inv.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        v,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hpc,
        inv,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => inv1 => Merge.all_inv(~d, l, hb, ho, ht, k, n, b0, o0, t0, v, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hb0, ho0, ht0, hpc, inv1)
      )
# a clash that is open after all the keys of a merge, or whose key is among no
# keys, is open
def Merge.open_final(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +k: Ledgers.Id,
  orr: Merge.Open(~d, lf, hf, n, k, [])
) -> {Vend.Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  match orr:
    case Merge.Or.Left{+op}:
      op
    case Merge.Or.Right{+c}:
      Empty.absurd({Vend.Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}, Shared.Bool.false_ne_true(c))

# a merge that keeps a resource as the value mo, and opens its clash, gives a
# tree that reads the resource that mo holds, and has the clash open
def Merge.clashes_inv(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +k: Ledgers.Id,
  +o: Maybe<&2, Requests.Res>,
  +mo: Maybe<&2, List<&2, U32>>,
  eo2: {Vend.Res.found(mo) == o: Maybe<&2, Requests.Res>},
  inv: Merge.Inv(~d, lf, hf, n, k, mo, [])
) -> Merge.And(
  {Vend.Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Vend.Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+fin, orr) = inv
  (
    %eo2: {Vend.Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
    Merge.find_res(~d, lf, hf, n, mo, fin),
    Merge.open_final(~d, lf, hf, n, k, orr)
  )

# the merge of the keys of a difference, among which is the key of a resource
# whose pick clashes, once the read of ours is known (fo)
def Merge.clashes_core.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +hin: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(n)) == True{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o)
) -> Merge.And(
  {Vend.Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Vend.Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  Merge.clashes_inv(
    ~d,
    lf,
    hf,
    n,
    k,
    o,
    mo,
    eo2,
    Merge.all_inv(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      n,
      b,
      o,
      th,
      mo,
      ks,
      l,
      ho,
      [],
      lf,
      hf,
      N,
      eall,
      {==},
      wf,
      held,
      hb0,
      ho0,
      ht0,
      hpc,
      (
        Replicas.Hist.find(~Requests.Ask.machine(), ~d, l, lf, ho, Vend.Key.res(n), mo, Merge.grows_of(~d, l, l, lf, [], N, {==}, wf, nd))(eo1),
        Merge.Or.Right{hin}
      )
    )
  )

# the merge of the keys of a difference, among which is the key of a resource
# whose pick clashes
def Merge.clashes_core(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<Vend.L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.And(
  {Vend.Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Vend.Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  Merge.clashes_core.at(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    b,
    o,
    th,
    ks,
    lf,
    hf,
    N,
    eall,
    wf,
    held,
    nd,
    hb0,
    ho0,
    ht0,
    hpc,
    Merge.clash_in_diff(
      ~d,
      l,
      ho,
      ht,
      n,
      ks,
      o,
      th,
      ediff,
      Merge.clash_diff(~d, l, b, o, th, hpc),
      Merge.find_some(~d, l, ho, n, o, ho0),
      Merge.find_some(~d, l, ht, n, th, ht0)
    ),
    Merge.find_some(~d, l, ho, n, o, ho0)
  )

# the merge of a resource whose pick clashes, as the work that the merge ends
# in, keeps ours and opens the clash in the ledger of its nodes
def Merge.clashes_final(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<Vend.L(d)>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<Vend.L(d)>>},
  +eroot: {Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>},
  +enodes: {Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>},
  +held: Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.And(
  {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  match W:
    case Work{+lf, +hf, +N}:
      %enodes: Merge.And(
        {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      %eroot: Merge.And(
        {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      %Merge.And.left(
        Merge.Puts(~d, l, lf, N),
        Merge.Nodes([], N),
        Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
      ): Merge.And(
        {Vend.Res.find(~d, _, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Vend.Clash.open(~d, _, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      Merge.clashes_core(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        ks,
        lf,
        hf,
        N,
        eall,
        Merge.And.left(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        hb0,
        ho0,
        ht0,
        hpc,
        ediff
      )

# a merge that gives an act, and whose pick of a resource clashes, once it is
# known what it has gone through, keeps ours, and opens the clash
def Merge.clashes_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  fs: Merge.Facts(~d, l, hb, ho, ht, k, h2, ns),
  +hb0: {Vend.Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> Merge.And(
  {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+ks, r1) = fs
  (+W, r2) = r1
  (+eall, r3) = r2
  (+eroot, r4) = r3
  (+enodes, r5) = r4
  (+ediff, held) = r5
  Merge.clashes_final(~d, l, hb, ho, ht, k, n, b, o, th, ks, W, h2, ns, eall, eroot, enodes, held, hb0, ho0, ht0, hpc, ediff)

# the pair of two Data
def Merge.to_pair(-A: Data, -B: Data, p: Merge.And(A, B)) -> A & B:
  match p:
    case Tuple{a, b}:
      (a, b)
# a merge that gives an act, and whose pick of a resource clashes, keeps ours
# for it, and opens its clash
def Merge.clashes_go(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>},
  +hb0: {Vend.Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Vend.Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Vend.Res.find(~d, l, Vend.Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {
  Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
}
  & {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.to_pair(
    {Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
    {Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>},
    Merge.clashes_facts(
      ~d,
      l,
      Base.tree(base),
      Replicas.Tip.content(t),
      Vend.Source.root(from),
      k,
      h2,
      ns,
      n,
      b,
      o,
      th,
      Merge.facts_go(~d, l, t, k, from, base, vs, h2, ns, e0),
      hb0,
      ho0,
      ht0,
      hpc
    )
  )

# the first of a pair
def Merge.fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case Tuple{a, b}:
      a

# a tree that lists whole reads each key finally, by the law of a tree
def Merge.final_look(
  -S: Data,
  -o: Trees.Tree.Ops(S),
  wh: Trees.Laws.Whole(S, o),
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  bs: List<&2, Trees.Binding>,
  e1: {Trees.Ops.range(S, o)(s)(h)([]) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  k: List<&2, U32>
) -> {Trees.Look.is_final(Trees.Ops.look(S, o)(s)(h)(k)) == True{}: Bool}:
  match wh:
    case Tuple{empty, w2}:
      Merge.fst(
        {Trees.Look.is_final(Trees.Ops.look(S, o)(s)(h)(k)) == True{}: Bool},
        (
          {Maybe.is_some(&2, Trees.Edit, Trees.Ops.put(S, o)(s)(h)(k)(None{})) == True{}: Bool}
            & {Maybe.is_some(&2, List<&2, Trees.Binding>, Trees.Ops.range(S, o)(s)(h)([])) == True{}: Bool}
        ),
        Merge.fst(
          (@k2: List<&2, U32> -> @m: Maybe<&2, List<&2, U32>> -> @p: List<&2, U32> -> {
            Trees.Look.is_final(Trees.Ops.look(S, o)(s)(h)(k2)) == True{}: Bool
          }
            & (
              {Maybe.is_some(&2, Trees.Edit, Trees.Ops.put(S, o)(s)(h)(k2)(m)) == True{}: Bool}
                & {Maybe.is_some(&2, List<&2, Trees.Binding>, Trees.Ops.range(S, o)(s)(h)(p)) == True{}: Bool}
            )),
          (@h3: Maybe<&2, Hashes.Hash> -> @bs3: List<&2, Trees.Binding> -> {
            Trees.Ops.range(S, o)(s)(h3)([]) == Some{bs3}: Maybe<&2, List<&2, Trees.Binding>>
          } -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Trees.Ops.diff(S, o)(s)(h)(h3)) == True{}: Bool}),
          w2(s)(h)(bs)(e1)
        )(k)(None{})([])
      )

# the clashes that a read of the key of the open clashes tells are some (the
# body of Clash.left, apart from the read)
def Merge.left_of(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> Maybe<&2, Bool>:
  Maybe.map(&2, List<&2, Resources.Name>, Bool, ns => Bool.not(List.is_empty(&2, Resources.Name, ns)), Merge.names_of(m))

# a final read of the clashes tells whether a resource still clashes, once the
# read is known (m)
def Merge.left_some.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.clashes(k)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  hm: {Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, m) == True{}: Bool}
) -> {Maybe.is_some(&2, Bool, Vend.Clash.left(~d, l, h, k)) == True{}: Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Bool, Vend.Clash.left(~d, l, h, k)) == True{}: Bool}, Shared.Bool.false_ne_true(hm))
    case Some{+v}:
      %Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.clashes(k)),
        Some{v},
        em
      ): {Maybe.is_some(&2, Bool, Merge.left_of(_)) == True{}: Bool}
      {==}

# a tree that lists whole tells whether a resource still clashes after a merge
def Answer.kn_range(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  +l2: Vend.L(d),
  +h2: Maybe<&2, Hashes.Hash>,
  r: Merge.Listed(~d, l2, h2)
) -> Vend.Answer.Known(~d, l, h, l2, h2):
  (+bs, e1) = r
  +k => p => Merge.left_some.at(
    ~d,
    l2,
    h2,
    k,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l2, h2, Vend.Key.clashes(k)),
    {==},
    Merge.final_look(
      Vend.L(d),
      Replicas.Led.tree(Requests.Ask.machine(), d),
      Merge.laws_whole(d),
      l2,
      h2,
      bs,
      e1,
      Vend.Key.clashes(k)
    )
  )

# a read of the clashes of a merge that told tells in a tree that the ledger
# holds whole
def Answer.kn_of_kept(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  +l2: Vend.L(d),
  +h2: Maybe<&2, Hashes.Hash>,
  hk: {Vend.Tree.kept(~d, l2, h2) == True{}: Bool}
) -> Vend.Answer.Known(~d, l, h, l2, h2):
  Answer.kn_range(~d, l, h, l2, h2, Merge.kept_range(~d, l2, h2, hk))

# what Node.head_kept says of the ledger d and the kernel kern
def Node.HeadKept(~d: Vend.Led(), ~kern: Vend.Kern(d)) -> Type:
  @l: Vend.L(d) -> @c: Ledgers.Line -> @t: Replicas.Tip -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}

# a merge never loses a change that only one side made: when the merge of a
# resource takes the content of one side (Pick.merge: theirs when ours is the
# base, ours when theirs is the base or both agree), the tree that a taken
# merge gives holds the resource with that content
law Merge.act_takes:
  for ~d: Vend.Led()
  for l: Vend.L(d)
  for t: Replicas.Tip
  for k: Ledgers.Id
  for from: Requests.Source
  for base: Maybe<&2, Requests.Source>
  for vs: Maybe<&2, List<&2, String>>
  for h2: Maybe<&2, Hashes.Hash>
  for ns: List<&2, List<&2, U32>>
  for n: Resources.Name
  for b: Maybe<&2, Requests.Res>
  for o: Maybe<&2, Requests.Res>
  for th: Maybe<&2, Requests.Res>
  for x: Maybe<&2, Requests.Res>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Vend.Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Vend.Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Vend.Res.find(~d, l, Vend.Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {
      Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>
    }
    -> {
      Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
        == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>
    }

def Merge.act_takes(d, l, t, k, from, base, vs, h2, ns, n, b, o, th, x):
  e0 => hb0 => ho0 => ht0 => hp => Merge.takes_go(~d, l, t, k, from, base, vs, h2, ns, n, b, o, th, x, e0, hb0, ho0, ht0, hp)

# a merge keeps what both sides hold the same, and opens a clash only where
# the merge of a resource clashes: when the merge of a resource clashes, the
# tree that a taken merge gives holds ours for it, and its clash is open
law Merge.act_clashes:
  for ~d: Vend.Led()
  for l: Vend.L(d)
  for t: Replicas.Tip
  for k: Ledgers.Id
  for from: Requests.Source
  for base: Maybe<&2, Requests.Source>
  for vs: Maybe<&2, List<&2, String>>
  for h2: Maybe<&2, Hashes.Hash>
  for ns: List<&2, List<&2, U32>>
  for n: Resources.Name
  for b: Maybe<&2, Requests.Res>
  for o: Maybe<&2, Requests.Res>
  for th: Maybe<&2, Requests.Res>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Vend.Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Vend.Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Vend.Res.find(~d, l, Vend.Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {
      Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>
    }
    -> (
      {
        Vend.Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
          == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
      }
        & {
          Vend.Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>
        }
    )

def Merge.act_clashes(d, l, t, k, from, base, vs, h2, ns, n, b, o, th):
  e0 => hb0 => ho0 => ht0 => hpc => Merge.clashes_go(~d, l, t, k, from, base, vs, h2, ns, n, b, o, th, e0, hb0, ho0, ht0, hpc)
