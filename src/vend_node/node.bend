import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ./answers.bend as Answers
import ./facts.bend as Facts
import ./shared/parts.bend as Parts
import ./spec.bend as Spec

# The state of a node
# -------------------
# A node holds its name, the writers connected to it, the resources mounted
# to it, whether it has stopped, its facts, and the parts of content that it
# keeps by hash. All that it answers is read from its facts. The name of a
# node is not reserved (it does not start with '~'): a reserved name is one
# under which a node says that its trust broke, and never the name of a node.

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
    facts: Facts.Facts(),
    parts: Parts.Parts
  }

# the facts fs are sound for the name name, and the name is not reserved
# (Facts.Trust.reserved): it can be the name of a node that holds fs
def Raw.sound(+name: String, fs: Facts.Facts()) -> Bool:
  Bool.and(Facts.Facts.ok(name, fs), Bool.not(Facts.Trust.reserved(name)))

# r can be a node: its facts are sound for its name, and its name is not
# reserved, so the name under which another node says that its trust broke is
# never the name of r
def Raw.ok(r: Raw) -> Bool:
  match r:
    case Raw{name, ws, ms, st, fs, ps}:
      Raw.sound(name, fs)

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
def Needs.of(+s: Facts.Facts(), +name: String, ms: List<&2, Mounted>) -> List<&2, Hashes.Hash>:
  match ms:
    case Nil{}:
      []
    case Con{Mounted{a, b, p}, rest}:
      Needs.put(Answers.View.at(s, name, b, p), Needs.of(s, name, rest))

# the id of the request by which the node name records what the resource at
# the address a held
def Mount.id(name: String, a: String) -> Ledgers.Id:
  Ledgers.Id{name, String.append("mount ", a)}
