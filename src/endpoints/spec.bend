import Base
import ../shared.bend as Shared

# An endpoint reaches resources of one kind. The core sees each resource
# as a stream: signals come in, commands go out. The endpoint alone reads
# the rest of a name; the core never assumes a path.

# Reachability
# ------------

# What the endpoint knows of a resource now. Present: reached, and it
# exists, with the token of its content. Absent: reached, and it does not
# exist. Unreachable: the endpoint cannot tell. Absent and Unreachable never
# stand for each other, and none of them is final.
type Reach is Data:
  Present{token: Shared.Bytes()}
  Absent{}
  Unreachable{reason: String}

# The stream
# ----------

# A signal from the endpoint. Reached: the reachability changed. Hinted: the
# resource may have changed; a hint is not data, so it only asks for a
# fetch. Fetched: the content and its token, as an answer to a fetch or on
# the endpoint's own. Overflowed: hints were lost, so fetch again.
type Signal is Data:
  Reached{state: Reach}
  Hinted{}
  Fetched{bytes: Shared.Bytes(), token: Shared.Bytes()}
  Overflowed{}

# What a writer believes is there before it writes.
type Expect is Data:
  WasPresent{token: Shared.Bytes()}
  WasAbsent{}

# A command to the endpoint. Fetch: send the content. Put: write bytes as
# the new content, believing e; the endpoint repeats the check of e against
# writers outside the core as well as its kind allows.
type Command is Data:
  Fetch{}
  Put{bytes: Shared.Bytes(), expect: Expect}

# A version for the history: new content, or the resource is gone.
type Version is Data:
  Content{bytes: Shared.Bytes(), token: Shared.Bytes()}
  Gone{}

# What a step does: send a command, or record a version.
type Effect is Data:
  Send{command: Command}
  Record{version: Version}

# What the core keeps of one stream. reach: the last known reachability.
# last: the token of the last recorded content, or None when the last
# record is Gone or there is none; it outlives Unreachable gaps, so the
# history stays whole. fetching: a fetch is out. dirty: a hint came while it
# was out, so fetch once more when it answers.
type Stream is Data:
  Stream{reach: Reach, last: Maybe<&2, Shared.Bytes()>, fetching: Bool, dirty: Bool}

# A stream that knows nothing yet.
def Stream.new() -> Stream:
  Stream{Unreachable{"not reached yet"}, None{}, False{}, False{}}

# the reachability that k knows
def Stream.reach(k: Stream) -> Reach:
  match k:
    case Stream{r, l, f, d}:
      r

# the token of the last content that k recorded
def Stream.last(k: Stream) -> Maybe<&2, Shared.Bytes()>:
  match k:
    case Stream{r, l, f, d}:
      l

# a fetch of k is out
def Stream.fetching(k: Stream) -> Bool:
  match k:
    case Stream{r, l, f, d}:
      f

# a hint came while the fetch of k was out
def Stream.dirty(k: Stream) -> Bool:
  match k:
    case Stream{r, l, f, d}:
      d

# The result of a step: the stream after it, and its effects in order.
type Stepped is Data:
  Stepped{stream: Stream, effects: List<&2, Effect>}

# t is the token of the last recorded content
def Stream.knows(last: Maybe<&2, Shared.Bytes()>, t: Shared.Bytes()) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{a}:
      Shared.Bytes.is_eq(a, t)

# a fetch, unless one is out: then fetch once more when it answers
def Stream.ask(r: Reach, last: Maybe<&2, Shared.Bytes()>, fetching: Bool) -> Stepped:
  match fetching:
    case False{}:
      Stepped{Stream{r, last, True{}, False{}}, [Send{Fetch{}}]}
    case True{}:
      Stepped{Stream{r, last, True{}, True{}}, []}

# the record of fetched content: none when t is the last recorded content
def Stream.record(
  last: Maybe<&2, Shared.Bytes()>,
  bytes: Shared.Bytes(),
  +t: Shared.Bytes()
) -> List<&2, Effect>:
  Shared.Bool.when(
    List<&2, Effect>,
    Stream.knows(last, t),
    u => [],
    u => [Record{Content{bytes, t}}]
  )

# after a fetch answered with bytes and token t: record them unless they
# are the last recorded content, and fetch again if a hint came meanwhile
def Stream.fetched(
  dirty: Bool,
  last: Maybe<&2, Shared.Bytes()>,
  bytes: Shared.Bytes(),
  +t: Shared.Bytes()
) -> Stepped:
  match dirty:
    case False{}:
      Stepped{Stream{Present{t}, Some{t}, False{}, False{}}, Stream.record(last, bytes, t)}
    case True{}:
      es = List.append(&2, Effect, Stream.record(last, bytes, t), [Send{Fetch{}}])
      Stepped{Stream{Present{t}, Some{t}, True{}, False{}}, es}

# A Reached answer of Absent or Unreachable ends a fetch that is out: the
# endpoint answers a fetch with Fetched or with Reached. If a hint came
# while it was out, fetch again; else nothing is out.

# the stream with reachability r and last recorded token last after a fetch
# ended, with effects es before a new fetch when dirty
def Stream.settle(
  r: Reach,
  last: Maybe<&2, Shared.Bytes()>,
  dirty: Bool,
  es: List<&2, Effect>
) -> Stepped:
  match dirty:
    case False{}:
      Stepped{Stream{r, last, False{}, False{}}, es}
    case True{}:
      Stepped{Stream{r, last, True{}, False{}}, List.append(&2, Effect, es, [Send{Fetch{}}])}

# after the resource is reached as absent: record Gone once, and end the
# fetch that is out
def Stream.absent(last: Maybe<&2, Shared.Bytes()>, dirty: Bool) -> Stepped:
  match last:
    case None{}:
      Stream.settle(Absent{}, None{}, dirty, [])
    case Some{a}:
      Stream.settle(Absent{}, None{}, dirty, [Record{Gone{}}])

# after the resource is reached as present with token t: fetch when t is
# not the last recorded content
def Stream.present(
  +last: Maybe<&2, Shared.Bytes()>,
  +fetching: Bool,
  dirty: Bool,
  +t: Shared.Bytes()
) -> Stepped:
  Shared.Bool.when(
    Stepped,
    Stream.knows(last, t),
    u => Stepped{Stream{Present{t}, last, fetching, dirty}, []},
    u => Stream.ask(Present{t}, last, fetching)
  )

# the stream after the signal, and the effects it causes
def Stream.step(k: Stream, s: Signal) -> Stepped:
  match k s:
    case Stream{r, l, f, d} Reached{Unreachable{w}}:
      Stream.settle(Unreachable{w}, l, d, [])
    case Stream{r, l, f, d} Reached{Absent{}}:
      Stream.absent(l, d)
    case Stream{r, l, f, d} Reached{Present{t}}:
      Stream.present(l, f, d, t)
    case Stream{r, l, f, d} Hinted{}:
      Stream.ask(r, l, f)
    case Stream{r, l, f, d} Overflowed{}:
      Stream.ask(r, l, f)
    case Stream{r, l, f, d} Fetched{b, t}:
      Stream.fetched(d, l, b, t)

# the belief e holds for k: k is not fetching, and it saw what e says:
# present with that token as its last recorded content, or absent. An
# Unreachable resource, or one with a fetch out, holds no belief.
def Expect.holds(e: Expect, k: Stream) -> Bool:
  match e k:
    case WasPresent{+a} Stream{Present{b}, Some{c}, False{}, d}:
      List.all.if(u => Shared.Bytes.is_eq(a, c), Shared.Bytes.is_eq(a, b))
    case WasAbsent{} Stream{Absent{}, l, False{}, d}:
      True{}
    case _ _:
      False{}

# Why a write through the core is refused: the stream it met.
type Refused is Data:
  Refused{now: Stream}

# the stream after an accepted write of bytes with token t that believes e:
# one Put, and the content recorded at once
def Stream.wrote(+bytes: Shared.Bytes(), +t: Shared.Bytes(), e: Expect) -> Stepped:
  Stepped{
    Stream{Present{t}, Some{t}, False{}, False{}},
    [Send{Put{bytes, e}}, Record{Content{bytes, t}}]
  }

# the stream after a write of bytes with token t that believes e, and its
# effects; or the refusal when e does not hold. Writes through the core are
# ordered by the core, so this check is exact.
def Stream.write(
  +k: Stream,
  bytes: Shared.Bytes(),
  t: Shared.Bytes(),
  +e: Expect
) -> Result<&2, &2, Refused, Stepped>:
  Shared.Bool.when(
    Result<&2, &2, Refused, Stepped>,
    Expect.holds(e, k),
    u => Done{Stream.wrote(bytes, t, e)},
    u => Fail{Refused{k}}
  )

# Laws
# ----

# the versions among effects
def Effect.versions(es: List<&2, Effect>) -> List<&2, Version>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Send{c}, t}:
      Effect.versions(t)
    case Con{Record{v}, t}:
      v <> Effect.versions(t)

# the commands among effects
def Effect.commands(es: List<&2, Effect>) -> List<&2, Command>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Send{c}, t}:
      c <> Effect.commands(t)
    case Con{Record{v}, t}:
      Effect.commands(t)

# the versions that a step records
def Stepped.versions(s: Stepped) -> List<&2, Version>:
  match s:
    case Stepped{k, es}:
      Effect.versions(es)

# the commands that a step sends
def Stepped.commands(s: Stepped) -> List<&2, Command>:
  match s:
    case Stepped{k, es}:
      Effect.commands(es)

# the stream after a step
def Stepped.stream(s: Stepped) -> Stream:
  match s:
    case Stepped{k, es}:
      k

# not knowing records nothing: an Unreachable signal adds no version
law unreachable_records_nothing:
  for k: Stream
  for why: String
  {Stepped.versions(Stream.step(k, Reached{Unreachable{why}})) == []: List<&2, Version>}

# losing touch forgets nothing: the last recorded content outlives it
law unreachable_keeps_last:
  for k: Stream
  for why: String
  {
    Stream.last(
      Stepped.stream(Stream.step(k, Reached{Unreachable{why}}))
    )
      == Stream.last(k): Maybe<&2, Shared.Bytes()>
  }

# a hint is not data: it records nothing
law hint_records_nothing:
  for k: Stream
  {Stepped.versions(Stream.step(k, Hinted{})) == []: List<&2, Version>}

# a hint sends at most one fetch, and none while one is out
law hint_fetches_once:
  for k: Stream
  {
    Nat.is_le(
      List.length(&2, Command, Stepped.commands(Stream.step(k, Hinted{}))),
      1n
    )
      == True{}: Bool
  }

# no hint is lost: after a hint, a fetch is out (new, or marked to run once
# more when the one out answers)
law hint_is_kept:
  for k: Stream
  {Stream.fetching(Stepped.stream(Stream.step(k, Hinted{}))) == True{}: Bool}

# content the core last recorded records nothing again
law same_content_records_nothing:
  for k: Stream
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for h: {Stream.knows(Stream.last(k), t) == True{}: Bool}
  {Stepped.versions(Stream.step(k, Fetched{bytes, t})) == []: List<&2, Version>}

# new content records exactly its version
law new_content_records_once:
  for k: Stream
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for h: {Stream.knows(Stream.last(k), t) == False{}: Bool}
  {Stepped.versions(Stream.step(k, Fetched{bytes, t})) == [Content{bytes, t}]: List<&2, Version>}

# a resource whose last record is content records Gone once when it is
# reached as absent
law absent_records_gone:
  for k: Stream
  for t: Shared.Bytes()
  for h: {Stream.last(k) == Some{t}: Maybe<&2, Shared.Bytes()>}
  {Stepped.versions(Stream.step(k, Reached{Absent{}})) == [Gone{}]: List<&2, Version>}

# a resource whose last record is Gone, or that has none, records nothing
# when it is reached as absent
law absent_stays_quiet:
  for k: Stream
  for h: {Stream.last(k) == None{}: Maybe<&2, Shared.Bytes()>}
  {Stepped.versions(Stream.step(k, Reached{Absent{}})) == []: List<&2, Version>}

# a write is refused exactly when its belief does not hold
law write_refused:
  for k: Stream
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for e: Expect
  {
    Result.is_fail(
      &2,
      &2,
      Refused,
      Stepped,
      Stream.write(k, bytes, t, e)
    )
      == Bool.not(Expect.holds(e, k)): Bool
  }

# an accepted write sends exactly one Put of its bytes and belief, and
# records exactly its content
law write_puts_and_records:
  for k: Stream
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for e: Expect
  for s: Stepped
  for h: {Stream.write(k, bytes, t, e) == Done{s}: Result<&2, &2, Refused, Stepped>}
  {Stepped.commands(s) == [Put{bytes, e}]: List<&2, Command>} &
    {Stepped.versions(s) == [Content{bytes, t}]: List<&2, Version>}

# after an accepted write, its fetch records nothing: the write recorded it
law write_then_fetch_quiet:
  for k: Stream
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for e: Expect
  for s: Stepped
  for h: {Stream.write(k, bytes, t, e) == Done{s}: Result<&2, &2, Refused, Stepped>}
  {Stepped.versions(Stream.step(Stepped.stream(s), Fetched{bytes, t})) == []: List<&2, Version>}

# a Reached answer of Absent or Unreachable ends the fetch that is out: a
# fetch is out after it exactly when a hint came while the old one was out
law absent_ends_fetch:
  for k: Stream
  {Stream.fetching(Stepped.stream(Stream.step(k, Reached{Absent{}}))) == Stream.dirty(k): Bool}

# the same for Unreachable
law unreachable_ends_fetch:
  for k: Stream
  for why: String
  {
    Stream.fetching(
      Stepped.stream(Stream.step(k, Reached{Unreachable{why}}))
    )
      == Stream.dirty(k): Bool
  }
