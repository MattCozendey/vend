import Base
import ../endpoints/spec.bend as Ep
import ../glob/impl.bend as GlobImpl
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../history/impl.bend as HistoryImpl
import ../history/spec.bend as History
import ../journal/spec.bend as Journal
import ../lines/impl.bend as LinesImpl
import ../lines/spec.bend as Lines
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../shared/tables.bend as Tables
import ../store/impl.bend as StoreImpl
import ../store/spec.bend as Store
import ./spec.bend as Spec

# The step
# --------

# c versions the file at path: Spec.Core.tracks, through the glob slots,
# whose cost grows only with the length of the path
def Core.tracks(c: Spec.Core, +path: String) -> Bool:
  match c:
    case Spec.Core{Spec.Mount{sp, ln, r, g, a}, s, h, l, ss, ms, ns}:
      mine = List.all.if(
        u => Bool.not(Spec.Core.under_any(ns, path)),
        Bool.not(String.eq(path, Spec.Mount.space_file()))
      )
      List.all.if(
        v => List.all.if(
          u => GlobImpl.Rule.selects.fast(g, path),
          Bool.and(Glob.is_path(path), mine)
        ),
        Bool.not(Spec.Core.under(path, Spec.Mount.checkouts_dir()))
      )

# Core.tracks answers what Spec.Core.tracks answers
def Core.tracks_ok(
  c: Spec.Core,
  +path: String
) -> {Core.tracks(c, path) == Spec.Core.tracks(c, path): Bool}:
  match c:
    case Spec.Core{Spec.Mount{sp, ln, r, g, a}, s, h, l, ss, ms, ns}:
      mine = List.all.if(
        u => Bool.not(Spec.Core.under_any(ns, path)),
        Bool.not(String.eq(path, Spec.Mount.space_file()))
      )
      here = Bool.and(Glob.is_path(path), mine)
      out = Bool.not(Spec.Core.under(path, Spec.Mount.checkouts_dir()))
      %GlobImpl.Rule.selects_fast_ok(
        g,
        path
      ): {
        List.all.if(
          v => List.all.if(u => GlobImpl.Rule.selects.fast(g, path), here),
          out
        )
          == List.all.if(v => List.all.if(u => _, here), out): Bool
      }
      {==}

# c with the stream k for the file at path
def Core.set_stream(c: Spec.Core, path: String, k: Ep.Stream) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h, l, Tables.Table.set(Ep.Stream, ss, path, k), ms, ns}

# c with the pending move of the file at path set to f
def Core.set_moved(c: Spec.Core, path: String, f: Maybe<&2, Resources.Name>) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h, l, ss, Tables.Table.set(Maybe<&2, Resources.Name>, ms, path, f), ns}

# c with the store s2
def Core.set_store(c: Spec.Core, s2: Store.Store) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s2, h, l, ss, ms, ns}

# c with the history h2 and the line l2
def Core.set_versions(c: Spec.Core, h2: History.History, l2: Lines.Line) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h2, l2, ss, ms, ns}

# c with the directory d starting another space
def Core.nest(c: Spec.Core, d: String) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h, l, ss, ms, d <> ns}

# the heads of the file at path on the line of c
def Core.heads(+c: Spec.Core, path: String) -> List<&2, Octets.Bytes()>:
  Lines.Line.heads(Spec.Core.line(c), Spec.Core.name(c, path))

# A version is kept whole or not at all: if the store, the history or the
# line refuses it, the step gives back c0, the core before the version,
# so a failed step changes nothing that the journal keeps.

# the step after the line took the node v (id x) by the author a of the
# file at path, or refused: the record of the version, then the version
def Core.advanced(
  c0: Spec.Core,
  c: Spec.Core,
  +path: String,
  h2: History.History,
  x: Octets.Bytes(),
  a: History.Author,
  content: Maybe<&2, Octets.Bytes()>,
  v: History.Node,
  r: Result<&2, &2, Lines.Refused, Lines.Line>
) -> Spec.Stepped:
  match r:
    case Done{+l2}:
      +c = c
      n = Spec.Core.name(c, path)
      rec = {Journal.Kept{Lines.Line.name(l2), content, v}: Journal.Record}
      Spec.Stepped{
        Core.set_moved(Core.set_versions(c, h2, l2), path, None{}),
        [Spec.Logged{rec}, Spec.Recorded{n, x, a}]
      }
    case Fail{e}:
      +c0 = c0
      Spec.Stepped{c0, [Spec.Failed{Spec.Core.name(c0, path), Spec.LineProblem{e}}]}

# the step after the history took the node v by the author a, or refused
def Core.added(
  +c0: Spec.Core,
  +c: Spec.Core,
  +path: String,
  parents: List<&2, Octets.Bytes()>,
  a: History.Author,
  content: Maybe<&2, Octets.Bytes()>,
  v: History.Node,
  r: Result<&2, &2, History.Refusal, History.Added>
) -> Spec.Stepped:
  match r:
    case Done{History.Added{+h2, +x}}:
      Core.advanced(
        c0,
        c,
        path,
        h2,
        x,
        a,
        content,
        v,
        Lines.Line.advance(Spec.Core.line(c), h2, Spec.Core.name(c, path), parents, x)
      )
    case Fail{e}:
      Spec.Stepped{c0, [Spec.Failed{Spec.Core.name(c0, path), Spec.HistoryProblem{e}}]}

# the step that keeps body, by the author a, as the next version of the file
# at path: its parents are the heads on the line, then the line moves to it;
# c0 is the core before the version, content its bytes (None for Gone)
def Core.keep(
  c0: Spec.Core,
  +c: Spec.Core,
  +path: String,
  body: History.Body,
  +a: History.Author,
  content: Maybe<&2, Octets.Bytes()>
) -> Spec.Stepped:
  +parents = Core.heads(c, path)
  +v = {
    History.Node{Spec.Core.name(c, path), parents, body, Spec.Core.moved(c, path), a}: History.Node
  }
  Core.added(c0, c, path, parents, a, content, v, History.History.add(Spec.Core.history(c), v))

# the step after the store took the content of the file at path, or failed
def Core.stored(
  +c: Spec.Core,
  path: String,
  r: Result<&2, &2, Store.Problem, Store.Wrote>,
  a: History.Author,
  content: Maybe<&2, Octets.Bytes()>
) -> Spec.Stepped:
  match r:
    case Fail{p}:
      Spec.Stepped{c, [Spec.Failed{Spec.Core.name(c, path), Spec.StoreProblem{p}}]}
    case Done{Store.Wrote{s2, root}}:
      Core.keep(c, Core.set_store(c, s2), path, History.Has{root}, a, content)

# the step that records the version v of the file at path, by the author
# a: content goes to the store, then to the history; Gone goes to the
# history
def Core.record(+c: Spec.Core, path: String, v: Ep.Version, a: History.Author) -> Spec.Stepped:
  match v:
    case Ep.Content{+bytes, t}:
      Core.stored(
        c,
        path,
        Store.Tree.write(Spec.Core.store(c), Spec.Core.items(bytes)),
        a,
        Some{bytes}
      )
    case Ep.Gone{}:
      Core.keep(c, c, path, History.Gone{}, a, None{})

# os in front of the outputs of s
def Core.prefix(os: List<&2, Spec.Output>, s: Spec.Stepped) -> Spec.Stepped:
  match s:
    case Spec.Stepped{c, rest}:
      Spec.Stepped{c, List.append(&2, Spec.Output, os, rest)}

# the outputs of r, then of k on the core after r
def Core.then(r: Spec.Stepped, k: Spec.Core -> Spec.Stepped) -> Spec.Stepped:
  match r:
    case Spec.Stepped{c, os}:
      Core.prefix(os, k(c))

# the step that carries out the effects of a stream, in order: a Send is a
# Command output, a Record is recorded by the author a
def Core.effects(
  es: List<&2, Ep.Effect>,
  c: Spec.Core,
  +path: String,
  +a: History.Author
) -> Spec.Stepped:
  match es:
    case Nil{}:
      Spec.Stepped{c, []}
    case Con{Ep.Send{k}, t}:
      Core.prefix([Spec.Command{path, k}], Core.effects(t, c, path, a))
    case Con{Ep.Record{v}, t}:
      Core.then(Core.record(c, path, v, a), c2 => Core.effects(t, c2, path, a))

# the step after the stream of the file at path stepped to s; what it
# records is by the author a
def Core.streamed(c: Spec.Core, +path: String, s: Ep.Stepped, a: History.Author) -> Spec.Stepped:
  match s:
    case Ep.Stepped{k, es}:
      Core.effects(es, Core.set_stream(c, path, k), path, a)

# the step after the signal s about the file at path: nothing for a file
# the core does not track; what an endpoint shows is by the author of the
# mount
def Core.noticed(+c: Spec.Core, +path: String, s: Ep.Signal) -> Spec.Stepped:
  Bools.Bool.when(
    Spec.Stepped,
    Core.tracks(c, path),
    u => Core.streamed(c, path, Ep.Stream.step(Spec.Core.stream(c, path), s), Spec.Core.author(c)),
    u => Spec.Stepped{c, []}
  )

# what the core believes is at a file: present with the token of the
# content it last recorded, or absent
def Core.belief(last: Maybe<&2, Octets.Bytes()>) -> Ep.Expect:
  match last:
    case None{}:
      Ep.WasAbsent{}
    case Some{t}:
      Ep.WasPresent{t}

# the step of an accepted write of b to the file at path. The history and
# the line are the truth for writes through the core (the heads already
# matched), so the write is recorded now and the endpoint is a mirror: the
# Put carries what the core last recorded, and the endpoint answers with
# what is really there.
def Core.wrote(+c: Spec.Core, +path: String, +b: Octets.Bytes(), a: History.Author) -> Spec.Stepped:
  e = Core.belief(Ep.Stream.last(Spec.Core.stream(c, path)))
  Core.streamed(c, path, Ep.Stream.wrote(b, Hash.Hash.blake3(b), e), a)

# the step of a write of b to the file at path by the agent named a, which
# saw the heads e on the line. Refused when e are not the heads on the line now;
# also refused, with the heads, for a file the core does not track, which
# it does not write.
def Core.write(
  +c: Spec.Core,
  +path: String,
  b: Octets.Bytes(),
  e: List<&2, Octets.Bytes()>,
  a: String
) -> Spec.Stepped:
  +heads = Core.heads(c, path)
  ok = List.all.if(u => Core.tracks(c, path), History.Ids.is_eq(e, heads))
  Bools.Bool.when(
    Spec.Stepped,
    ok,
    u => Core.wrote(c, path, b, History.Agent{a}),
    u => Spec.Stepped{c, [Spec.Refused{Spec.Core.name(c, path), heads}]}
  )

def Spec.Core.step(c, i):
  match i:
    case Spec.Noticed{p, s}:
      Core.noticed(c, p, s)
    case Spec.Moved{f, t}:
      +c = c
      Spec.Stepped{Core.set_moved(c, t, Some{Spec.Core.name(c, f)}), []}
    case Spec.Nested{d}:
      Spec.Stepped{Core.nest(c, d), []}
    case Spec.Asked{Spec.Write{p, b, e, a}}:
      Core.write(c, p, b, e, a)
    case Spec.Asked{Spec.Stop{}}:
      Spec.Stepped{c, [Spec.Stopped{}]}

def Spec.untracked_ignored(c, p, s, h):
  Equal.sym(
    Spec.Stepped,
    Spec.Stepped{c, []},
    Spec.Core.step(c, Spec.Noticed{p, s}),
    (%Equal.sym(
      Bool,
      Core.tracks(c, p),
      Spec.Core.tracks(c, p),
      Core.tracks_ok(c, p)
    ): {
      Spec.Stepped{
        c,
        []
      }
        == Bools.Bool.when(
          Spec.Stepped,
          _,
          u => Core.streamed(c, p, Ep.Stream.step(Spec.Core.stream(c, p), s), Spec.Core.author(c)),
          u => Spec.Stepped{c, []}
        ): Spec.Stepped
    }; (%Equal.sym(
      Bool,
      Spec.Core.tracks(c, p),
      False{},
      h
    ): {
      Spec.Stepped{
        c,
        []
      }
        == Bools.Bool.when(
          Spec.Stepped,
          _,
          u => Core.streamed(c, p, Ep.Stream.step(Spec.Core.stream(c, p), s), Spec.Core.author(c)),
          u => Spec.Stepped{c, []}
        ): Spec.Stepped
    }; {==}))
  )

def Spec.write_refused(c, p, b, e, a, h):
  %Equal.sym(
    Bool,
    History.Ids.is_eq(
      e,
      Lines.Line.heads(Spec.Core.line(c), Resources.Name{Spec.Core.space(c), p})
    ),
    False{},
    h
  ):
    {
      Bools.Bool.when(
        Spec.Stepped,
        List.all.if(u => Core.tracks(c, p), _),
        u => Core.wrote(c, p, b, History.Agent{a}),
        u => Spec.Stepped{
          c,
          [
            Spec.Refused{
              Spec.Core.name(c, p),
              Lines.Line.heads(Spec.Core.line(c), Resources.Name{Spec.Core.space(c), p})
            }
          ]
        }
      )
        == Spec.Stepped{
          c,
          [
            Spec.Refused{
              Resources.Name{Spec.Core.space(c), p},
              Lines.Line.heads(Spec.Core.line(c), Resources.Name{Spec.Core.space(c), p})
            }
          ]
        }: Spec.Stepped
    }
  {==}

# after a move to t, the core remembers where t came from
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- the second uses sit in the rewrite motive of Moved.kept; the checker accepts them
def Moved.kept(
  +c: Spec.Core,
  f: String,
  t: String
) -> {
  Spec.Core.moved(
    Core.set_moved(c, t, Some{Spec.Core.name(c, f)}),
    t
  )
    == Some{Spec.Core.name(c, f)}: Maybe<&2, Resources.Name>
}:
  match c:
    case Spec.Core{m, s, h, l, ss, +ms, ns}:
      nm = Spec.Core.name(Spec.Core{m, s, h, l, ss, ms, ns}, f)
      %Equal.sym(
        Maybe<&2, Maybe<&2, Resources.Name>>,
        Tables.Table.get(
          Maybe<&2, Resources.Name>,
          Tables.Table.set(Maybe<&2, Resources.Name>, ms, t, Some{nm}),
          t
        ),
        Some{Some{nm}},
        Tables.Table.get_after_set(Maybe<&2, Resources.Name>, ms, t, Some{nm})
      ): {
        Maybe.default(
          &2,
          Maybe<&2, Resources.Name>,
          _,
          None{}
        )
          == Some{nm}: Maybe<&2, Resources.Name>
      }
      {==}

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.move_remembered(c, f, t):
  ({==}, Moved.kept(c, f, t))

# Replay
# ------

# the store a write left, or s when it failed
def Replay.wrote(s: Store.Store, r: Result<&2, &2, Store.Problem, Store.Wrote>) -> Store.Store:
  match r:
    case Done{Store.Wrote{s2, root}}:
      s2
    case Fail{e}:
      s

# the store after the content of a record, if any
def Replay.store(s: Store.Store, content: Maybe<&2, Octets.Bytes()>) -> Store.Store:
  match content:
    case None{}:
      s
    case Some{b}:
      +s = s
      Replay.wrote(s, Store.Tree.write(s, Spec.Core.items(b)))

# the history an add left, or h when it refused
def Replay.history(
  h: History.History,
  r: Result<&2, &2, History.Refusal, History.Added>
) -> History.History:
  match r:
    case Done{History.Added{h2, x}}:
      h2
    case Fail{e}:
      h

# the line an advance left, or l when it refused
def Replay.line(l: Lines.Line, r: Result<&2, &2, Lines.Refused, Lines.Line>) -> Lines.Line:
  match r:
    case Done{l2}:
      l2
    case Fail{e}:
      l

# the line after the node v, added to h, when the record is of the line
# named ln: the same advance the step made. It expects the heads the line
# follows now: a version's parents are exactly those heads, a merge node
# has them among its parents, and a line moved onto an existing node (a
# merge that only catches up) has that node descend from them.
def Replay.advance(+l: Lines.Line, h: History.History, ln: String, +v: History.Node) -> Lines.Line:
  +n = History.Node.name(v)
  Bools.Bool.when(
    Lines.Line,
    String.eq(ln, Lines.Line.name(l)),
    u => Replay.line(l, Lines.Line.advance(l, h, n, Lines.Line.heads(l, n), History.Node.id(v))),
    u => l
  )

# c after one record; the records of seen markers, marks and forks are the
# daemon's, and leave a core as it is
def Replay.one(c: Spec.Core, r: Journal.Record) -> Spec.Core:
  match c r:
    case Spec.Core{m, s, +h, l, ss, ms, ns} Journal.Kept{ln, content, +v}:
      +h2 = Replay.history(h, History.History.add(h, v))
      Spec.Core{m, Replay.store(s, content), h2, Replay.advance(l, h2, ln, v), ss, ms, ns}
    case k Journal.Saw{a, ln}:
      k
    case k Journal.Marked{ln, nm, msg, a}:
      k
    case k Journal.Forked{ln, f, mk}:
      k

# c after the records rs, in order
def Replay.all(rs: List<&2, Journal.Record>, c: Spec.Core) -> Spec.Core:
  match rs:
    case Nil{}:
      c
    case Con{r, t}:
      Replay.all(t, Replay.one(c, r))

def Spec.Core.replay(c, rs):
  Replay.all(rs, c)

# the bytes of items, one after another
def Replay.bytes(items: List<&2, Octets.Bytes()>) -> Octets.Bytes():
  match items:
    case Nil{}:
      []
    case Con{x, t}:
      List.append(&2, U32, x, Replay.bytes(t))

# the stream primed with the content that the store gives for root, if any
def Replay.primed.read(r: Maybe<&2, List<&2, Octets.Bytes()>>) -> Maybe<&2, Ep.Stream>:
  match r:
    case None{}:
      None{}
    case Some{items}:
      Some{
        Ep.Stream{
          Ep.Unreachable{"not reached yet"},
          Some{Hash.Hash.blake3(Replay.bytes(items))},
          False{},
          False{}
        }
      }

# the stream primed with the content of the node, when it holds content
def Replay.primed.node(s: Store.Store, v: Maybe<&2, History.Node>) -> Maybe<&2, Ep.Stream>:
  match v:
    case Some{History.Node{n, ps, History.Has{root}, f, a}}:
      Replay.primed.read(Store.Tree.read(s, root))
    case _:
      None{}

# the stream primed with the content of the one head xs, if there is one
def Replay.primed(
  s: Store.Store,
  h: History.History,
  xs: List<&2, Octets.Bytes()>
) -> Maybe<&2, Ep.Stream>:
  match xs:
    case Con{x, Nil{}}:
      Replay.primed.node(s, History.History.get(h, x))
    case _:
      None{}

# ss with k at p, when there is one
def Replay.put(
  ss: Tables.Table<Ep.Stream>,
  p: String,
  k: Maybe<&2, Ep.Stream>
) -> Tables.Table<Ep.Stream>:
  match k:
    case None{}:
      ss
    case Some{x}:
      Tables.Table.set(Ep.Stream, ss, p, x)

# streams with a primed stream for each path of ps whose one head on the
# line l holds content
def Replay.prime(
  ps: List<&2, String>,
  +s: Store.Store,
  +h: History.History,
  +l: Lines.Line,
  +sp: String,
  ss: Tables.Table<Ep.Stream>
) -> Tables.Table<Ep.Stream>:
  match ps:
    case Nil{}:
      ss
    case Con{+p, t}:
      k = Replay.primed(s, h, Lines.Line.heads(l, Resources.Name{sp, p}))
      Replay.prime(t, s, h, l, sp, Replay.put(ss, p, k))

# the heads of l, by path
def Replay.heads(l: Lines.Line) -> Tables.Table<List<&2, Octets.Bytes()>>:
  match l:
    case Lines.Line{sp, nm, hs}:
      hs

# c with its streams primed from its line
def Replay.primed.core(c: Spec.Core) -> Spec.Core:
  match c:
    case Spec.Core{Spec.Mount{+sp, ln, r, g, a}, +s, +h, +l, ss, ms, ns}:
      ps = Tables.Table.keys(List<&2, Octets.Bytes()>, Replay.heads(l))
      Spec.Core{Spec.Mount{sp, ln, r, g, a}, s, h, l, Replay.prime(ps, s, h, l, sp, ss), ms, ns}

def Spec.Core.restore(m, rs):
  Replay.primed.core(Spec.Core.replay(Spec.Core.new(m), rs))

def Spec.checkouts_untracked(c, p, u):
  match c:
    case Spec.Core{Spec.Mount{sp, ln, r, g, a}, s, h, l, ss, ms, ns}:
      +p = p
      mine = List.all.if(
        w => Bool.not(Spec.Core.under_any(ns, p)),
        Bool.not(String.eq(p, Spec.Mount.space_file()))
      )
      %Equal.sym(Bool, Spec.Core.under(p, Spec.Mount.checkouts_dir()), True{}, u):
        {
          List.all.if(
            v => List.all.if(w => Glob.Rule.selects(g, p), Bool.and(Glob.is_path(p), mine)),
            Bool.not(_)
          )
            == False{}: Bool
        }
      {==}
