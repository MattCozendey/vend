import Base
import ../endpoints/spec.bend as Ep
import ../glob/impl.bend as GlobImpl
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../history/impl.bend as HistoryImpl
import ../history/spec.bend as History
import ../lines/impl.bend as LinesImpl
import ../lines/spec.bend as Lines
import ../shared.bend as Shared
import ../store/impl.bend as StoreImpl
import ../store/spec.bend as Store
import ./spec.bend as Spec

# The step
# --------

# c versions the file at path: Spec.Core.tracks, through the glob slots,
# whose cost grows only with the length of the path
def Core.tracks(c: Spec.Core, +path: String) -> Bool:
  match c:
    case Spec.Core{Spec.Mount{sp, ln, r, g}, s, h, l, ss, ms, ns}:
      mine = List.all.if(
        u => Bool.not(Spec.Core.under_any(ns, path)),
        Bool.not(String.eq(path, Spec.Mount.space_file()))
      )
      List.all.if(u => GlobImpl.Rule.selects.fast(g, path), Bool.and(Glob.is_path(path), mine))

# Core.tracks answers what Spec.Core.tracks answers
def Core.tracks_ok(
  c: Spec.Core,
  +path: String
) -> {Core.tracks(c, path) == Spec.Core.tracks(c, path): Bool}:
  match c:
    case Spec.Core{Spec.Mount{sp, ln, r, g}, s, h, l, ss, ms, ns}:
      mine = List.all.if(
        u => Bool.not(Spec.Core.under_any(ns, path)),
        Bool.not(String.eq(path, Spec.Mount.space_file()))
      )
      here = Bool.and(Glob.is_path(path), mine)
      %GlobImpl.Rule.selects_fast_ok(
        g,
        path
      ): {
        List.all.if(
          u => GlobImpl.Rule.selects.fast(g, path),
          here
        )
          == List.all.if(u => _, here): Bool
      }
      {==}

# c with the stream k for the file at path
def Core.set_stream(c: Spec.Core, path: String, k: Ep.Stream) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h, l, Map.set(&2, Ep.Stream, ss, path, k), ms, ns}

# c with the pending move of the file at path set to f
def Core.set_moved(c: Spec.Core, path: String, f: Maybe<&2, Shared.Name>) -> Spec.Core:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Spec.Core{m, s, h, l, ss, Map.set(&2, Maybe<&2, Shared.Name>, ms, path, f), ns}

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
def Core.heads(+c: Spec.Core, path: String) -> List<&2, Shared.Bytes()>:
  Lines.Line.heads(Spec.Core.line(c), Spec.Core.name(c, path))

# the step after the line took the node x of the file at path, or refused
def Core.advanced(
  c: Spec.Core,
  +path: String,
  h2: History.History,
  x: Shared.Bytes(),
  r: Result<&2, &2, Lines.Refused, Lines.Line>
) -> Spec.Stepped:
  match r:
    case Done{l2}:
      +c = c
      n = Spec.Core.name(c, path)
      Spec.Stepped{
        Core.set_moved(Core.set_versions(c, h2, l2), path, None{}),
        [Spec.Recorded{n, x}]
      }
    case Fail{e}:
      +c = c
      Spec.Stepped{c, [Spec.Failed{Spec.Core.name(c, path), Spec.LineProblem{e}}]}

# the step after the history took the node, or lacked a parent
def Core.added(
  +c: Spec.Core,
  +path: String,
  parents: List<&2, Shared.Bytes()>,
  r: Result<&2, &2, History.Missing, History.Added>
) -> Spec.Stepped:
  match r:
    case Done{History.Added{+h2, +x}}:
      Core.advanced(
        c,
        path,
        h2,
        x,
        Lines.Line.advance(Spec.Core.line(c), h2, Spec.Core.name(c, path), parents, x)
      )
    case Fail{e}:
      Spec.Stepped{c, [Spec.Failed{Spec.Core.name(c, path), Spec.HistoryProblem{e}}]}

# the step that keeps body as the next version of the file at path: its
# parents are the heads on the line, then the line moves to it
def Core.keep(+c: Spec.Core, +path: String, body: History.Body) -> Spec.Stepped:
  +parents = Core.heads(c, path)
  v = {History.Node{Spec.Core.name(c, path), parents, body, Spec.Core.moved(c, path)}: History.Node}
  Core.added(c, path, parents, History.History.add(Spec.Core.history(c), v))

# the step after the store took the content of the file at path, or failed
def Core.stored(
  +c: Spec.Core,
  path: String,
  r: Result<&2, &2, Store.Problem, Store.Wrote>
) -> Spec.Stepped:
  match r:
    case Fail{p}:
      Spec.Stepped{c, [Spec.Failed{Spec.Core.name(c, path), Spec.StoreProblem{p}}]}
    case Done{Store.Wrote{s2, root}}:
      Core.keep(Core.set_store(c, s2), path, History.Has{root})

# the step that records the version v of the file at path: content goes to
# the store, then to the history; Gone goes to the history
def Core.record(+c: Spec.Core, path: String, v: Ep.Version) -> Spec.Stepped:
  match v:
    case Ep.Content{bytes, t}:
      Core.stored(c, path, Store.Tree.write(Spec.Core.store(c), Spec.Core.items(bytes)))
    case Ep.Gone{}:
      Core.keep(c, path, History.Gone{})

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
# Command output, a Record is recorded
def Core.effects(es: List<&2, Ep.Effect>, c: Spec.Core, +path: String) -> Spec.Stepped:
  match es:
    case Nil{}:
      Spec.Stepped{c, []}
    case Con{Ep.Send{k}, t}:
      Core.prefix([Spec.Command{path, k}], Core.effects(t, c, path))
    case Con{Ep.Record{v}, t}:
      Core.then(Core.record(c, path, v), c2 => Core.effects(t, c2, path))

# the step after the stream of the file at path stepped to s
def Core.streamed(c: Spec.Core, +path: String, s: Ep.Stepped) -> Spec.Stepped:
  match s:
    case Ep.Stepped{k, es}:
      Core.effects(es, Core.set_stream(c, path, k), path)

# the step after the signal s about the file at path: nothing for a file
# the core does not track
def Core.noticed(+c: Spec.Core, +path: String, s: Ep.Signal) -> Spec.Stepped:
  Shared.Bool.when(
    Spec.Stepped,
    Core.tracks(c, path),
    u => Core.streamed(c, path, Ep.Stream.step(Spec.Core.stream(c, path), s)),
    u => Spec.Stepped{c, []}
  )

# what the core believes is at a file: present with the token of the
# content it last recorded, or absent
def Core.belief(last: Maybe<&2, Shared.Bytes()>) -> Ep.Expect:
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
def Core.wrote(+c: Spec.Core, +path: String, +b: Shared.Bytes()) -> Spec.Stepped:
  e = Core.belief(Ep.Stream.last(Spec.Core.stream(c, path)))
  Core.streamed(c, path, Ep.Stream.wrote(b, Hash.Hash.blake3(b), e))

# the step of a write of b to the file at path by a writer that saw the
# heads e on the line. Refused when e are not the heads on the line now;
# also refused, with the heads, for a file the core does not track, which
# it does not write.
def Core.write(
  +c: Spec.Core,
  +path: String,
  b: Shared.Bytes(),
  e: List<&2, Shared.Bytes()>
) -> Spec.Stepped:
  +heads = Core.heads(c, path)
  ok = List.all.if(u => Core.tracks(c, path), History.Ids.is_eq(e, heads))
  Shared.Bool.when(
    Spec.Stepped,
    ok,
    u => Core.wrote(c, path, b),
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
    case Spec.Asked{Spec.Write{p, b, e}}:
      Core.write(c, p, b, e)
    case Spec.Asked{Spec.Stop{}}:
      Spec.Stepped{c, [Spec.Stopped{}]}
