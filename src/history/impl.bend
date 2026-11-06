import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ./spec.bend as Spec

# An add stores the node under its id and makes it a tip of its resource in
# place of its parents; a node that is there already changes nothing.
# History.join is not written yet.

# a before b, by bytes: the first differing byte decides; a prefix comes
# first
def Ids.lt(a: Shared.Bytes(), b: Shared.Bytes()) -> Bool:
  match a b:
    case Nil{} Con{y, yt}:
      True{}
    case Con{+x, xt} Con{+y, yt}:
      Shared.Bool.when(Bool, U32.is_eq(x, y), u => Ids.lt(xt, yt), u => (x < y: U32))
    case _ _:
      False{}

# xs, sorted ascending, with x, once
def Ids.insert(+x: Shared.Bytes(), xs: List<&2, Shared.Bytes()>) -> List<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      [x]
    case Con{+y, +t}:
      Shared.Bool.when(
        List<&2, Shared.Bytes()>,
        Shared.Bytes.is_eq(x, y),
        u => Con{y, t},
        u => Shared.Bool.when(
          List<&2, Shared.Bytes()>,
          Ids.lt(x, y),
          v => Con{x, Con{y, t}},
          v => Con{y, Ids.insert(x, t)}
        )
      )

# xs without the ids of ps
def Ids.without(
  xs: List<&2, Shared.Bytes()>,
  +ps: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Shared.Bool.when(
        List<&2, Shared.Bytes()>,
        Spec.Ids.has(ps, x),
        u => Ids.without(t, ps),
        u => Con{x, Ids.without(t, ps)}
      )

# the first id of xs that h lacks, or None
def Ids.missing(+h: Spec.History, xs: List<&2, Shared.Bytes()>) -> Maybe<&2, Shared.Bytes()>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Bytes()>,
        Spec.History.has(h, x),
        u => Ids.missing(h, t),
        u => Some{x}
      )

# h with the node v under its id x, a tip of its resource in place of its
# parents
def History.put(h: Spec.History, +x: Shared.Bytes(), +v: Spec.Node) -> Spec.History:
  match h:
    case Spec.History{ns, +ts}:
      +key = Shared.Name.show(Spec.Node.name(v))
      old = Maybe.default(
        &2,
        List<&2, Shared.Bytes()>,
        Shared.Table.get(List<&2, Shared.Bytes()>, ts, key),
        []
      )
      tips = Ids.insert(x, Ids.without(old, Spec.Node.parents(v)))
      nodes = Shared.Table.set(Spec.Node, ns, Hash.Hash.hex(x), v)
      Spec.History{nodes, Shared.Table.set(List<&2, Shared.Bytes()>, ts, key, tips)}

# the add of v under its id x, given what h holds there: a node that h
# holds already changes nothing, and another node there is a collision
def History.add.at(
  h: Spec.History,
  +v: Spec.Node,
  +x: Shared.Bytes(),
  m: Maybe<&2, Spec.Node>
) -> Result<&2, &2, Spec.Refusal, Spec.Added>:
  match m:
    case None{}:
      Done{Spec.Added{History.put(h, x, v), x}}
    case Some{+w}:
      Shared.Bool.when(
        Result<&2, &2, Spec.Refusal, Spec.Added>,
        Spec.Node.same(w, v),
        u => Done{Spec.Added{h, x}},
        u => Fail{Spec.Collides{w, v}}
      )

# the add of v, given the missing parent if any
def History.add.of(
  +h: Spec.History,
  +v: Spec.Node,
  miss: Maybe<&2, Shared.Bytes()>
) -> Result<&2, &2, Spec.Refusal, Spec.Added>:
  match miss:
    case Some{p}:
      Fail{Spec.Missing{p}}
    case None{}:
      +x = Spec.Node.id(v)
      History.add.at(h, v, x, Spec.History.get(h, x))

def Spec.History.add(h, v):
  +h = h
  +v = v
  History.add.of(h, v, Ids.missing(h, Spec.Node.parents(v)))

# Proofs
# ------
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it

# the history in the answer of an add, or a new one for a refusal
def Added.history(r: Result<&2, &2, Spec.Refusal, Spec.Added>) -> Spec.History:
  match r:
    case Fail{e}:
      Spec.History.new()
    case Done{Spec.Added{g, x}}:
      g

# no refusal is an add
def Added.not_fail(
  -e: Spec.Refusal,
  -r: Spec.Added,
  a: {Fail{e} == Done{r}: Result<&2, &2, Spec.Refusal, Spec.Added>}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.cong(
      Result<&2, &2, Spec.Refusal, Spec.Added>,
      Bool,
      q => Result.is_done(&2, &2, Spec.Refusal, Spec.Added, q),
      Fail{e},
      Done{r},
      a
    )
  )

# put keeps the tips of every other resource
def Frames.put(
  h: Spec.History,
  x: Shared.Bytes(),
  +v: Spec.Node,
  m: Shared.Name
) -> {
  String.eq(Shared.Name.show(Spec.Node.name(v)), Shared.Name.show(m)) == False{}: Bool
} -> {
  Spec.History.tips(History.put(h, x, v), m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>
}:
  match h:
    case Spec.History{ns, +ts}:
      d =>
        +key = Shared.Name.show(Spec.Node.name(v))
        old = Maybe.default(
          &2,
          List<&2, Shared.Bytes()>,
          Shared.Table.get(List<&2, Shared.Bytes()>, ts, key),
          []
        )
        +tips = Ids.insert(x, Ids.without(old, Spec.Node.parents(v)))
        +k2 = Shared.Name.show(m)
        %Equal.sym(
          Maybe<&2, List<&2, Shared.Bytes()>>,
          Shared.Table.get(
            List<&2, Shared.Bytes()>,
            Shared.Table.set(List<&2, Shared.Bytes()>, ts, key, tips),
            k2
          ),
          Shared.Table.get(List<&2, Shared.Bytes()>, ts, k2),
          Shared.Table.set_keeps_other(List<&2, Shared.Bytes()>, ts, key, tips, k2, d)
        ): {
          Maybe.default(
            &2,
            List<&2, Shared.Bytes()>,
            _,
            []
          )
            == Maybe.default(
              &2,
              List<&2, Shared.Bytes()>,
              Shared.Table.get(List<&2, Shared.Bytes()>, ts, k2),
              []
            ): List<&2, Shared.Bytes()>
        }
        {==}

# add_frames where h holds the node w under the id, with b the answer of
# Node.same(w, v)
def Frames.same(
  h: Spec.History,
  v: Spec.Node,
  m: Shared.Name,
  g: Spec.History,
  -x: Shared.Bytes(),
  -w: Spec.Node,
  b: Bool
) -> {
  Shared.Bool.when(
    Result<&2, &2, Spec.Refusal, Spec.Added>,
    b,
    u => Done{Spec.Added{h, Spec.Node.id(v)}},
    u => Fail{Spec.Collides{w, v}}
  )
    == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {Spec.History.tips(g, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>}:
  match b:
    case True{}:
      a =>
        hg = {
          Equal.cong(
            Result<&2, &2, Spec.Refusal, Spec.Added>,
            Spec.History,
            Added.history,
            Done{Spec.Added{h, Spec.Node.id(v)}},
            Done{Spec.Added{g, x}},
            a
          ): {h == g: Spec.History}
        }
        %hg: {Spec.History.tips(_, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>}
        {==}
    case False{}:
      a => Empty.absurd(
        {Spec.History.tips(g, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>},
        Added.not_fail(Spec.Collides{w, v}, Spec.Added{g, x}, a)
      )

# add_frames once the add got past the parent check, with r what h holds
# under the id
def Frames.at(
  +h: Spec.History,
  +v: Spec.Node,
  m: Shared.Name,
  g: Spec.History,
  -x: Shared.Bytes(),
  r: Maybe<&2, Spec.Node>
) -> {
  History.add.at(
    h,
    v,
    Spec.Node.id(v),
    r
  )
    == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {
  String.eq(Shared.Name.show(Spec.Node.name(v)), Shared.Name.show(m)) == False{}: Bool
} -> {Spec.History.tips(g, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>}:
  match r:
    case None{}:
      a => d =>
        +p = History.put(h, Spec.Node.id(v), v)
        hg = {
          Equal.cong(
            Result<&2, &2, Spec.Refusal, Spec.Added>,
            Spec.History,
            Added.history,
            Done{Spec.Added{p, Spec.Node.id(v)}},
            Done{Spec.Added{g, x}},
            a
          ): {p == g: Spec.History}
        }
        %hg: {Spec.History.tips(_, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>}
        Frames.put(h, Spec.Node.id(v), v, m)(d)
    case Some{w}:
      a => d => Frames.same(h, v, m, g, x, w, Spec.Node.same(w, v))(a)

# add_frames given the missing parent, if any
def Frames.of(
  +h: Spec.History,
  +v: Spec.Node,
  m: Shared.Name,
  g: Spec.History,
  x: Shared.Bytes(),
  miss: Maybe<&2, Shared.Bytes()>
) -> {
  History.add.of(h, v, miss) == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {
  String.eq(Shared.Name.show(Spec.Node.name(v)), Shared.Name.show(m)) == False{}: Bool
} -> {Spec.History.tips(g, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>}:
  match miss:
    case Some{p}:
      a => d => Empty.absurd(
        {Spec.History.tips(g, m) == Spec.History.tips(h, m): List<&2, Shared.Bytes()>},
        Added.not_fail(Spec.Missing{p}, Spec.Added{g, x}, a)
      )
    case None{}:
      a => d => Frames.at(h, v, m, g, x, Spec.History.get(h, Spec.Node.id(v)))(a, d)

def Spec.add_frames(h, v, g, x, m, a, d):
  +h = h
  +v = v
  +m = m
  Frames.of(
    h,
    v,
    m,
    g,
    x,
    Ids.missing(h, Spec.Node.parents(v))
  )(a, Shared.String.eq_flip(Shared.Name.show(m), Shared.Name.show(Spec.Node.name(v)))(d))

# an id that h lacks has another hex than an id that h holds, with c the
# answer of String.eq on the two hexes
def Keeps.ne(
  h: Spec.History,
  x: Shared.Bytes(),
  y: Shared.Bytes(),
  -w: Spec.Node,
  c: Bool
) -> {
  String.eq(Hash.Hash.hex(x), Hash.Hash.hex(y)) == c: Bool
} -> {
  Spec.History.get(h, x) == None{}: Maybe<&2, Spec.Node>
} -> {Spec.History.get(h, y) == Some{w}: Maybe<&2, Spec.Node>} -> {c == False{}: Bool}:
  match h c:
    case hh False{}:
      _ => _ => _ => {==}
    case Spec.History{ns, ts} True{}:
      e => n => o =>
        +hx = Hash.Hash.hex(x)
        +hy = Hash.Hash.hex(y)
        xy = Shared.String.eq_sound(hx, hy)(e)
        yw = Equal.cong(
          Maybe<&2, Spec.Node>,
          Bool,
          q => Maybe.is_some(&2, Spec.Node, q),
          Some{w},
          Shared.Table.get(Spec.Node, ns, hy),
          Equal.sym(Maybe<&2, Spec.Node>, Shared.Table.get(Spec.Node, ns, hy), Some{w}, o)
        )
        yx = Equal.cong(
          String,
          Bool,
          k => Maybe.is_some(&2, Spec.Node, Shared.Table.get(Spec.Node, ns, k)),
          hy,
          hx,
          Equal.sym(String, hx, hy, xy)
        )
        xn = Equal.cong(
          Maybe<&2, Spec.Node>,
          Bool,
          q => Maybe.is_some(&2, Spec.Node, q),
          Shared.Table.get(Spec.Node, ns, hx),
          None{},
          n
        )
        tx = Equal.trans(
          Bool,
          True{},
          Maybe.is_some(&2, Spec.Node, Shared.Table.get(Spec.Node, ns, hy)),
          Maybe.is_some(&2, Spec.Node, Shared.Table.get(Spec.Node, ns, hx)),
          yw,
          yx
        )
        Equal.trans(
          Bool,
          True{},
          Maybe.is_some(&2, Spec.Node, Shared.Table.get(Spec.Node, ns, hx)),
          False{},
          tx,
          xn
        )

# put keeps every node under another hex
def Keeps.put(
  h: Spec.History,
  x: Shared.Bytes(),
  v: Spec.Node,
  y: Shared.Bytes(),
  -w: Spec.Node
) -> {
  String.eq(Hash.Hash.hex(x), Hash.Hash.hex(y)) == False{}: Bool
} -> {
  Spec.History.get(h, y) == Some{w}: Maybe<&2, Spec.Node>
} -> {Spec.History.get(History.put(h, x, v), y) == Some{w}: Maybe<&2, Spec.Node>}:
  match h:
    case Spec.History{ns, ts}:
      d => o =>
        +hx = Hash.Hash.hex(x)
        +hy = Hash.Hash.hex(y)
        %Equal.sym(
          Maybe<&2, Spec.Node>,
          Shared.Table.get(Spec.Node, Shared.Table.set(Spec.Node, ns, hx, v), hy),
          Shared.Table.get(Spec.Node, ns, hy),
          Shared.Table.set_keeps_other(Spec.Node, ns, hx, v, hy, d)
        ): {_ == Some{w}: Maybe<&2, Spec.Node>}
        o

# add_keeps where h holds the node w2 under the id, with b the answer of
# Node.same(w2, v)
def Keeps.same(
  h: Spec.History,
  v: Spec.Node,
  g: Spec.History,
  -x: Shared.Bytes(),
  y: Shared.Bytes(),
  -w: Spec.Node,
  -w2: Spec.Node,
  b: Bool
) -> {
  Shared.Bool.when(
    Result<&2, &2, Spec.Refusal, Spec.Added>,
    b,
    u => Done{Spec.Added{h, Spec.Node.id(v)}},
    u => Fail{Spec.Collides{w2, v}}
  )
    == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {
  Spec.History.get(h, y) == Some{w}: Maybe<&2, Spec.Node>
} -> {Spec.History.get(g, y) == Some{w}: Maybe<&2, Spec.Node>}:
  match b:
    case True{}:
      a => o =>
        hg = {
          Equal.cong(
            Result<&2, &2, Spec.Refusal, Spec.Added>,
            Spec.History,
            Added.history,
            Done{Spec.Added{h, Spec.Node.id(v)}},
            Done{Spec.Added{g, x}},
            a
          ): {h == g: Spec.History}
        }
        %hg: {Spec.History.get(_, y) == Some{w}: Maybe<&2, Spec.Node>}
        o
    case False{}:
      a => o => Empty.absurd(
        {Spec.History.get(g, y) == Some{w}: Maybe<&2, Spec.Node>},
        Added.not_fail(Spec.Collides{w2, v}, Spec.Added{g, x}, a)
      )

# add_keeps once the add got past the parent check, with r what h holds
# under the id
def Keeps.at(
  +h: Spec.History,
  +v: Spec.Node,
  g: Spec.History,
  -x: Shared.Bytes(),
  +y: Shared.Bytes(),
  -w: Spec.Node,
  r: Maybe<&2, Spec.Node>
) -> {
  Spec.History.get(h, Spec.Node.id(v)) == r: Maybe<&2, Spec.Node>
} -> {
  History.add.at(
    h,
    v,
    Spec.Node.id(v),
    r
  )
    == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {
  Spec.History.get(h, y) == Some{w}: Maybe<&2, Spec.Node>
} -> {Spec.History.get(g, y) == Some{w}: Maybe<&2, Spec.Node>}:
  match r:
    case None{}:
      er => a => +o =>
        +id = Spec.Node.id(v)
        +p = History.put(h, id, v)
        hg = {
          Equal.cong(
            Result<&2, &2, Spec.Refusal, Spec.Added>,
            Spec.History,
            Added.history,
            Done{Spec.Added{p, id}},
            Done{Spec.Added{g, x}},
            a
          ): {p == g: Spec.History}
        }
        %hg: {Spec.History.get(_, y) == Some{w}: Maybe<&2, Spec.Node>}
        d = Keeps.ne(h, id, y, w, String.eq(Hash.Hash.hex(id), Hash.Hash.hex(y)))({==}, er, o)
        Keeps.put(h, id, v, y, w)(d, o)
    case Some{w2}:
      er => a => o => Keeps.same(h, v, g, x, y, w, w2, Spec.Node.same(w2, v))(a, o)

# add_keeps given the missing parent, if any
def Keeps.of(
  +h: Spec.History,
  +v: Spec.Node,
  g: Spec.History,
  x: Shared.Bytes(),
  y: Shared.Bytes(),
  -w: Spec.Node,
  miss: Maybe<&2, Shared.Bytes()>
) -> {
  History.add.of(h, v, miss) == Done{Spec.Added{g, x}}: Result<&2, &2, Spec.Refusal, Spec.Added>
} -> {
  Spec.History.get(h, y) == Some{w}: Maybe<&2, Spec.Node>
} -> {Spec.History.get(g, y) == Some{w}: Maybe<&2, Spec.Node>}:
  match miss:
    case Some{p}:
      a => o => Empty.absurd(
        {Spec.History.get(g, y) == Some{w}: Maybe<&2, Spec.Node>},
        Added.not_fail(Spec.Missing{p}, Spec.Added{g, x}, a)
      )
    case None{}:
      a => o => Keeps.at(h, v, g, x, y, w, Spec.History.get(h, Spec.Node.id(v)))({==}, a, o)

def Spec.add_keeps(h, v, g, x, y, w, a, o):
  +h = h
  +v = v
  Keeps.of(h, v, g, x, y, w, Ids.missing(h, Spec.Node.parents(v)))(a, o)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
