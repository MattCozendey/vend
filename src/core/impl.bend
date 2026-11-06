import Base
import ../endpoints/spec.bend as Ep
import ../glob/impl.bend as GlobImpl
import ../hash/spec.bend as Hash
import ../history/impl.bend as HistoryImpl
import ../history/spec.bend as History
import ../shared.bend as Shared
import ../store/impl.bend as StoreImpl
import ../store/spec.bend as Store
import ./spec.bend as Spec

# The step
# --------

# c versions n: Spec.Core.tracks, through the glob slots, whose cost grows
# only with the length of n's path
def Core.tracks(c: Spec.Core, n: Shared.Name) -> Bool:
  match c n:
    case Spec.Core{tr, s, h, ss, ms} Shared.Name{Shared.FileScheme{}, rest}:
      GlobImpl.Rule.selects.fast(tr, rest)

# Core.tracks answers what Spec.Core.tracks answers
def Core.tracks_ok(
  c: Spec.Core,
  n: Shared.Name
) -> {Core.tracks(c, n) == Spec.Core.tracks(c, n): Bool}:
  match c n:
    case Spec.Core{tr, s, h, ss, ms} Shared.Name{Shared.FileScheme{}, rest}:
      GlobImpl.Rule.selects_fast_ok(tr, rest)

# c with the stream k for n
def Core.set_stream(c: Spec.Core, n: Shared.Name, k: Ep.Stream) -> Spec.Core:
  match c:
    case Spec.Core{tr, s, h, ss, ms}:
      Spec.Core{tr, s, h, Map.set(&2, Ep.Stream, ss, Shared.Name.show(n), k), ms}

# c with the pending move of n set to m
def Core.set_moved(c: Spec.Core, n: Shared.Name, m: Maybe<&2, Shared.Name>) -> Spec.Core:
  match c:
    case Spec.Core{tr, s, h, ss, ms}:
      Spec.Core{tr, s, h, ss, Map.set(&2, Maybe<&2, Shared.Name>, ms, Shared.Name.show(n), m)}

# c with the store s2
def Core.set_store(c: Spec.Core, s2: Store.Store) -> Spec.Core:
  match c:
    case Spec.Core{tr, s, h, ss, ms}:
      Spec.Core{tr, s2, h, ss, ms}

# c with the history h2
def Core.set_history(c: Spec.Core, h2: History.History) -> Spec.Core:
  match c:
    case Spec.Core{tr, s, h, ss, ms}:
      Spec.Core{tr, s, h2, ss, ms}

# the heads of n in c
def Core.heads(c: Spec.Core, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  History.History.heads(Spec.Core.history(c), n)

# the step after a commit of n: its node the one head, and the pending move
# of n used up. The commit's heads are the heads now, so it is never
# refused; a refusal would still be reported, not hidden.
def Core.committed(
  c: Spec.Core,
  +n: Shared.Name,
  r: Result<&2, &2, History.Refused, History.Committed>
) -> Spec.Stepped:
  match r:
    case Done{History.Committed{h2, x}}:
      Spec.Stepped{Core.set_moved(Core.set_history(c, h2), n, None{}), [Spec.Recorded{n, x}]}
    case Fail{History.Refused{hs}}:
      Spec.Stepped{c, [Spec.Refused{n, hs}]}

# the step that commits body as the next version of n, after the heads of
# now, with the pending move of n
def Core.commit(+c: Spec.Core, +n: Shared.Name, body: History.Body) -> Spec.Stepped:
  r = History.History.commit(Spec.Core.history(c), n, Core.heads(c, n), body, Spec.Core.moved(c, n))
  Core.committed(c, n, r)

# the step after the store took the content of n, or failed to
def Core.stored(
  c: Spec.Core,
  n: Shared.Name,
  r: Result<&2, &2, Store.Problem, Store.Wrote>
) -> Spec.Stepped:
  match r:
    case Fail{p}:
      Spec.Stepped{c, [Spec.Failed{n, p}]}
    case Done{Store.Wrote{s2, root}}:
      Core.commit(Core.set_store(c, s2), n, History.Has{root})

# the step that records the version v of n: content goes to the store,
# then to the history; Gone goes to the history
def Core.record(+c: Spec.Core, n: Shared.Name, v: Ep.Version) -> Spec.Stepped:
  match v:
    case Ep.Content{bytes, t}:
      Core.stored(c, n, Store.Tree.write(Spec.Core.store(c), Spec.Core.items(bytes)))
    case Ep.Gone{}:
      Core.commit(c, n, History.Gone{})

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

# the step that carries out the effects of n's stream, in order: a Send is
# a Command output, a Record is recorded
def Core.effects(es: List<&2, Ep.Effect>, c: Spec.Core, +n: Shared.Name) -> Spec.Stepped:
  match es:
    case Nil{}:
      Spec.Stepped{c, []}
    case Con{Ep.Send{k}, t}:
      Core.prefix([Spec.Command{n, k}], Core.effects(t, c, n))
    case Con{Ep.Record{v}, t}:
      Core.then(Core.record(c, n, v), c2 => Core.effects(t, c2, n))

# the step after n's stream stepped to s
def Core.streamed(c: Spec.Core, +n: Shared.Name, s: Ep.Stepped) -> Spec.Stepped:
  match s:
    case Ep.Stepped{k, es}:
      Core.effects(es, Core.set_stream(c, n, k), n)

# the step after the signal s about n: nothing for an untracked resource
def Core.noticed(+c: Spec.Core, +n: Shared.Name, s: Ep.Signal) -> Spec.Stepped:
  Shared.Bool.when(
    Spec.Stepped,
    Core.tracks(c, n),
    u => Core.streamed(c, n, Ep.Stream.step(Spec.Core.stream(c, n), s)),
    u => Spec.Stepped{c, []}
  )

# what the core believes is at a resource: present with the token of the
# content it last recorded, or absent
def Core.belief(last: Maybe<&2, Shared.Bytes()>) -> Ep.Expect:
  match last:
    case None{}:
      Ep.WasAbsent{}
    case Some{t}:
      Ep.WasPresent{t}

# the step of an accepted write of b to n. The core's history is the source
# of truth for writes through it (the heads already matched), so the write
# is recorded now and the endpoint is a mirror: the Put carries what the
# core last recorded, and the endpoint answers with what is really there.
def Core.wrote(+c: Spec.Core, +n: Shared.Name, +b: Shared.Bytes()) -> Spec.Stepped:
  e = Core.belief(Ep.Stream.last(Spec.Core.stream(c, n)))
  Core.streamed(c, n, Ep.Stream.wrote(b, Hash.Hash.blake3(b), e))

# the step of a write of b to n by a writer that saw the heads e. Refused
# when e are not the heads now; also refused, with the heads, for a
# resource the core does not track, which it does not write.
def Core.write(
  +c: Spec.Core,
  +n: Shared.Name,
  b: Shared.Bytes(),
  e: List<&2, Shared.Bytes()>
) -> Spec.Stepped:
  +heads = Core.heads(c, n)
  ok = List.all.if(u => Core.tracks(c, n), History.Ids.is_eq(e, heads))
  Shared.Bool.when(
    Spec.Stepped,
    ok,
    u => Core.wrote(c, n, b),
    u => Spec.Stepped{c, [Spec.Refused{n, heads}]}
  )

def Spec.Core.step(c, i):
  match i:
    case Spec.Noticed{n, s}:
      Core.noticed(c, n, s)
    case Spec.Moved{f, t}:
      Spec.Stepped{Core.set_moved(c, t, Some{f}), []}
    case Spec.Asked{Spec.Write{n, b, e}}:
      Core.write(c, n, b, e)
    case Spec.Asked{Spec.Stop{}}:
      Spec.Stepped{c, [Spec.Stopped{}]}
