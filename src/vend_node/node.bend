import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./run/answers.bend as Answers
import ./run/content.bend as Contents
import ./run/facts.bend as Facts
import ./run/parts.bend as Parts
import ./run/set.bend as Checks
import ./run/work.bend as Works
import ./spec.bend as Spec
import ./types.bend as Types

# The state of a node
# -------------------
# A node holds its name, the writers connected to it, the resources mounted
# to it, whether it has stopped, its facts, and the parts of content that it
# keeps by hash. All that it answers is read from its facts. The name of a
# node is not reserved (it does not start with '~'): a reserved name is one
# under which a node says that its trust broke, and never the name of a node.
# The facts and the parts are plain maps: this file and the files of run/
# that it imports are the code that runs, and hold no proof.

# a resource mounted to a node: its address, and the path of a branch where
# it is mounted
type Mounted is Data:
  Mounted{address: String, branch: Ledgers.Line, path: String}

# what a node holds
type Raw is Data:
  Raw{
    name: String,
    writers: List<&2, String>,
    mounts: List<&2, Mounted>,
    stopped: Bool,
    facts: Facts.Plain(),
    parts: Parts.Parts
  }

# the map fs is a set of facts (it is well formed, and each fact sits under
# its own key), and the map of the parts ps is well formed. The code that runs
# keeps this and builds no proof of it; impl.bend proves that each deed keeps
# it (Node.does_sound)
def Raw.set(+fs: Facts.Plain(), ps: Parts.Parts) -> Bool:
  Bool.and(
    Bool.and(
      Crits.Crit.wf(~Types.Fact, fs, 0n),
      Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
    ),
    Parts.Parts.wf(ps)
  )

# the facts fs and the parts ps are well formed maps, the facts are sound for
# the name name, and the name is not reserved (Facts.Trust.reserved): it can
# be the name of a node that holds fs and ps
def Raw.sound(+name: String, +fs: Facts.Plain(), ps: Parts.Parts) -> Bool:
  Bool.and(
    Raw.set(fs, ps),
    Bool.and(Facts.Facts.ok(name, fs), Bool.not(Facts.Trust.reserved(name)))
  )

# r can be a node: its facts are a set and are sound for its name, its parts
# are a well formed map, and its name is not reserved, so the name under
# which another node says that its trust broke is never the name of r
def Raw.ok(r: Raw) -> Bool:
  match r:
    case Raw{name, ws, ms, st, fs, ps}:
      Raw.sound(name, fs, ps)

# the address of the mounted resource m
def Mounted.address(m: Mounted) -> String:
  match m:
    case Mounted{a, b, p}:
      a

# the addresses of the mounted resources ms
def Mounts.addresses(ms: List<&2, Mounted>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{m, rest}:
      Mounted.address(m) <> Mounts.addresses(rest)

# the mounted resources ms but those at the address a
def Mounts.remove(ms: List<&2, Mounted>, +a: String) -> List<&2, Mounted>:
  match ms:
    case Nil{}:
      []
    case Con{+m, rest}:
      List.filter.put(
        Mounted,
        m,
        Mounts.remove(rest, a),
        Bool.not(String.eq(Mounted.address(m), a))
      )

# the words that the request r brings, if any
def Request.content(r: Spec.Request) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Spec.Request.Write{b, p, w}:
      w
    case Spec.Request.Resolve{m, p, w}:
      w
    case _:
      None{}

# the parts ps with the words m, if any
def Kept.with(ps: Parts.Parts, m: Maybe<&2, List<&2, U32>>) -> Parts.Parts:
  match m:
    case None{}:
      ps
    case Some{ws}:
      Parts.Parts.put(ps, ws)

# the hash of the words m, if any, before rest
def Needs.put(
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  rest: List<&2, Hashes.Hash>
) -> List<&2, Hashes.Hash>:
  match m:
    case Some{Some{ws}}:
      Hashes.Sha.hash(ws) <> rest
    case _:
      rest

# the hashes of the parts that the node name needs: what it reads at each of
# the mounted resources ms
def Needs.of(+s: Facts.Plain(), +name: String, ms: List<&2, Mounted>) -> List<&2, Hashes.Hash>:
  match ms:
    case Nil{}:
      []
    case Con{Mounted{a, b, p}, rest}:
      Needs.put(Answers.View.at(s, name, b, p), Needs.of(s, name, rest))

# the id of the request by which the node name records what the resource at
# the address a held
def Mount.id(name: String, a: String) -> Ledgers.Id:
  Ledgers.Id{name, String.append("mount ", a)}

# What a node does
# ----------------
# This is the code that runs: a deed takes a plain state to a plain state,
# and no proof is built on the way. impl.bend pairs a state with the proof
# that it is sound (Raw.ok) only to state and prove the laws of the spec; it
# proves there that a deed keeps a sound state sound (Node.does_sound), so a
# node that runs on plain states holds what the laws say.

# what a node does next, on plain states: the deeds of the spec, where the
# other node of a Sync is its state
type Act is Data:
  Act.Connect{writer: String}
  Act.Leave{writer: String}
  Act.Ask{id: Ledgers.Id, request: Spec.Request}
  Act.Sync{from: Raw}
  Act.Mount{address: String, branch: Ledgers.Line, path: String, held: List<&2, U32>}
  Act.Unmount{address: String}
  Act.Work{}
  Act.Drop{}
  Act.Stop{force: Bool}

# the state of a node of the name name, that holds nothing yet
def Raw.new(name: String) -> Raw:
  Raw{name, [], [], False{}, Facts.Facts.new(), Parts.Parts.new()}

# the state after the node takes in the request r of the id i, with the words
# of r to keep, when it may (go): it has not stopped, and the writer is
# connected
def Raw.asks(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Mounted>,
  st: Bool,
  fs: Facts.Plain(),
  ps: Parts.Parts,
  i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> Raw:
  match go:
    case False{}:
      Raw{name, ws, ms, st, fs, ps}
    case True{}:
      Raw{name, ws, ms, st, Facts.Facts.ask(name, fs, i, r), Kept.with(ps, Request.content(r))}

# the state after a work, unless the node has stopped
def Raw.works(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Mounted>,
  st: Bool,
  fs: Facts.Plain(),
  ps: Parts.Parts
) -> Raw:
  match st:
    case True{}:
      Raw{name, ws, ms, True{}, fs, ps}
    case False{}:
      Raw{name, ws, ms, False{}, Works.Work.does(fs, name), ps}

# the state r after the deed a
def Raw.does(r: Raw, a: Act) -> Raw:
  match r a:
    case Raw{name, +ws, ms, st, fs, ps} Act.Connect{+w}:
      Raw{name, w <> Shared.List.remove(~String, ~String.eq, ws, w), ms, st, fs, ps}
    case Raw{name, ws, ms, st, fs, ps} Act.Leave{w}:
      Raw{name, Shared.List.remove(~String, ~String.eq, ws, w), ms, st, fs, ps}
    case Raw{name, +ws, ms, +st, fs, ps} Act.Ask{+i, q}:
      Raw.asks(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        i,
        q,
        Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
      )
    case Raw{+name, ws, ms, st, fs, ps} Act.Sync{Raw{name2, ws2, ms2, st2, fs2, ps2}}:
      Raw{
        name,
        ws,
        ms,
        st,
        Facts.Facts.take_all(name, Facts.Facts.list(fs2), fs),
        Parts.Parts.join(ps, ps2)
      }
    case Raw{+name, ws, ms, +st, fs, ps} Act.Mount{+a, +b, +p, held}:
      Raw.asks(
        name,
        ws,
        Mounted{a, b, p} <> Mounts.remove(ms, a),
        st,
        fs,
        ps,
        Mount.id(name, a),
        Spec.Request.Write{b, p, Some{held}},
        Bool.not(st)
      )
    case Raw{name, ws, ms, st, fs, ps} Act.Unmount{a}:
      Raw{name, ws, Mounts.remove(ms, a), st, fs, ps}
    case Raw{name, ws, ms, st, fs, ps} Act.Work{}:
      Raw.works(name, ws, ms, st, fs, ps)
    case Raw{+name, ws, +ms, st, +fs, ps} Act.Drop{}:
      Raw{name, ws, ms, st, fs, Parts.Parts.only(ps, Needs.of(fs, name, ms))}
    case Raw{name, +ws, +ms, st, fs, ps} Act.Stop{f}:
      Raw{
        name,
        ws,
        ms,
        Bool.or(
          st,
          Bool.or(
            f,
            Bool.and(List.is_empty(&2, String, ws), List.is_empty(&2, String, Mounts.addresses(ms)))
          )
        ),
        fs,
        ps
      }

# What a node shows
# -----------------
# What the code that runs reads from a plain state. impl.bend proves that it
# is what the spec says of the node (Node.answer_runs, ...).

# the facts of the state r
def Raw.facts(r: Raw) -> Facts.Plain():
  match r:
    case Raw{name, ws, ms, st, fs, ps}:
      fs

# the state r holds the change c
def Raw.holds(r: Raw, c: Types.Change) -> Bool:
  Facts.Facts.holds(Raw.facts(r), c)

# the words of the resource at the path p in version k of the line c, as the
# state r reads them
def Raw.read(r: Raw, c: Ledgers.Line, k: Nat, p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Contents.Content.read(Raw.facts(r), c, k, p)

# the words of the resource at the path p of the branch b, as the state r
# shows them to the writer w
def Raw.view(r: Raw, w: String, b: Ledgers.Line, p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Answers.View.at(Raw.facts(r), w, b, p)

# the reply of the state r to the question q
def Raw.answer(r: Raw, q: Spec.Question) -> Maybe<&2, Spec.Reply>:
  Answers.Answer.of(Raw.facts(r), q)

# the voters that the state r proves to be liars
def Raw.liars(r: Raw) -> List<&2, String>:
  Facts.Facts.liars(Raw.facts(r))

# the hashes of the parts that the state r holds, each once
def Raw.parts(r: Raw) -> List<&2, Hashes.Hash>:
  match r:
    case Raw{name, ws, ms, st, fs, ps}:
      Parts.Parts.list(ps)

# the words of the hash h, if the state r holds them
def Raw.part(r: Raw, h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Raw{name, ws, ms, st, fs, ps}:
      Parts.Parts.get(ps, h)
