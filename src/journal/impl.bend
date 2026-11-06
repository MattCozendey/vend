import Base
import ../history/spec.bend as History
import ../shared.bend as Shared
import ../store/spec.bend as Store
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text
import ./spec.bend as Spec

# The reader: one entry at a time, from the start, until an entry is torn,
# fails its check, or does not decode; what came before it is the good part.

# A value read from the front of some bytes, and the bytes after it.
type Got<-T: Data> is Data:
  Got{value: T, rest: Shared.Bytes()}

# k of what m read, or None when m read nothing
def Got.then(
  -A: Data,
  -B: Data,
  m: Maybe<&2, Got<A>>,
  k: A -> Shared.Bytes() -> Maybe<&2, Got<B>>
) -> Maybe<&2, Got<B>>:
  match m:
    case None{}:
      None{}
    case Some{Got{v, r}}:
      k(v, r)

# the LEB128 number at the front of b, given acc so far and the weight of
# its next seven bits
def Leb.read.go(b: Shared.Bytes(), +weight: Nat, acc: Nat) -> Maybe<&2, Got<Nat>>:
  match b:
    case Nil{}:
      None{}
    case Con{+x, +t}:
      +n = Nat.add(acc, Nat.mul(U32.to_nat((x .&. 127: U32)), weight))
      Shared.Bool.when(
        Maybe<&2, Got<Nat>>,
        (x < 128: U32),
        u => Some{Got{n, t}},
        u => Leb.read.go(t, Nat.mul(weight, 128n), n)
      )

# the LEB128 number at the front of b
def Leb.read(b: Shared.Bytes()) -> Maybe<&2, Got<Nat>>:
  Leb.read.go(b, 1n, 0n)

# x in front of the bytes that m read
def Bytes.read.more(x: U32, m: Maybe<&2, Got<Shared.Bytes()>>) -> Maybe<&2, Got<Shared.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{Got{v, r}}:
      Some{Got{x <> v, r}}

# the first n bytes of b, or None when b is shorter
def Bytes.read(n: Nat, b: Shared.Bytes()) -> Maybe<&2, Got<Shared.Bytes()>>:
  match n:
    case 0n:
      Some{Got{[], b}}
    case 1n+k:
      match b:
        case Nil{}:
          None{}
        case Con{x, t}:
          Bytes.read.more(x, Bytes.read(k, t))

# framed bytes: their length, then them
def Framed.read(b: Shared.Bytes()) -> Maybe<&2, Got<Shared.Bytes()>>:
  Got.then(Nat, Shared.Bytes(), Leb.read(b), n => r => Bytes.read(n, r))

# the text that m read as UTF-8, or None when it is not UTF-8
def Utf8.got(m: Maybe<&2, String>, r: Shared.Bytes()) -> Maybe<&2, Got<String>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{Got{s, r}}

# framed UTF-8 text
def Utf8.read(b: Shared.Bytes()) -> Maybe<&2, Got<String>>:
  Got.then(Shared.Bytes(), String, Framed.read(b), x => r => Utf8.got(Text.Text.decode(x), r))

# a name: its space, then its path
def Name.read(b: Shared.Bytes()) -> Maybe<&2, Got<Shared.Name>>:
  Got.then(
    String,
    Shared.Name,
    Utf8.read(b),
    sp => r => Got.then(
      String,
      Shared.Name,
      Utf8.read(r),
      p => r2 => Some{Got{Shared.Name{sp, p}, r2}}
    )
  )

# x in front of the ids that m read
def Ids.read.cons(
  x: Shared.Bytes(),
  m: Maybe<&2, Got<List<&2, Shared.Bytes()>>>
) -> Maybe<&2, Got<List<&2, Shared.Bytes()>>>:
  match m:
    case None{}:
      None{}
    case Some{Got{v, r}}:
      Some{Got{x <> v, r}}

# n framed ids, in order
def Ids.read.go(n: Nat, b: Shared.Bytes()) -> Maybe<&2, Got<List<&2, Shared.Bytes()>>>:
  match n:
    case 0n:
      Some{Got{[], b}}
    case 1n+k:
      Got.then(
        Shared.Bytes(),
        List<&2, Shared.Bytes()>,
        Framed.read(b),
        x => r => Ids.read.cons(x, Ids.read.go(k, r))
      )

# ids: their number, then each framed
def Ids.read(b: Shared.Bytes()) -> Maybe<&2, Got<List<&2, Shared.Bytes()>>>:
  Got.then(Nat, List<&2, Shared.Bytes()>, Leb.read(b), n => r => Ids.read.go(n, r))

# a body: 0 then a root (its hash framed, then its count), or 1 for Gone
def Body.read(b: Shared.Bytes()) -> Maybe<&2, Got<History.Body>>:
  match b:
    case Con{0, r}:
      Got.then(
        Shared.Bytes(),
        History.Body,
        Framed.read(r),
        h => r2 => Got.then(
          Nat,
          History.Body,
          Leb.read(r2),
          c => r3 => Some{Got{History.Has{Store.Ref{h, c}}, r3}}
        )
      )
    case Con{1, r}:
      Some{Got{History.Gone{}, r}}
    case _:
      None{}

# a moved-from name: 0 for none, or 1 then a name
def From.read(b: Shared.Bytes()) -> Maybe<&2, Got<Maybe<&2, Shared.Name>>>:
  match b:
    case Con{0, r}:
      Some{Got{None{}, r}}
    case Con{1, r}:
      Got.then(Shared.Name, Maybe<&2, Shared.Name>, Name.read(r), n => r2 => Some{Got{Some{n}, r2}})
    case _:
      None{}

# an author: 0 for Outside, or 1 then the agent's name
def Author.read(b: Shared.Bytes()) -> Maybe<&2, Got<History.Author>>:
  match b:
    case Con{0, r}:
      Some{Got{History.Outside{}, r}}
    case Con{1, r}:
      Got.then(String, History.Author, Utf8.read(r), n => r2 => Some{Got{History.Agent{n}, r2}})
    case _:
      None{}

# a node: name, parents, body, moved-from, then author
def Node.read(b: Shared.Bytes()) -> Maybe<&2, Got<History.Node>>:
  Got.then(
    Shared.Name,
    History.Node,
    Name.read(b),
    n => r => Got.then(
      List<&2, Shared.Bytes()>,
      History.Node,
      Ids.read(r),
      ps => r2 => Got.then(
        History.Body,
        History.Node,
        Body.read(r2),
        bd => r3 => Got.then(
          Maybe<&2, Shared.Name>,
          History.Node,
          From.read(r3),
          f => r4 => Got.then(
            History.Author,
            History.Node,
            Author.read(r4),
            a => r5 => Some{Got{History.Node{n, ps, bd, f, a}, r5}}
          )
        )
      )
    )
  )

# a content: 0 for none, or 1 then framed bytes
def Content.read(b: Shared.Bytes()) -> Maybe<&2, Got<Maybe<&2, Shared.Bytes()>>>:
  match b:
    case Con{0, r}:
      Some{Got{None{}, r}}
    case Con{1, r}:
      Got.then(
        Shared.Bytes(),
        Maybe<&2, Shared.Bytes()>,
        Framed.read(r),
        x => r2 => Some{Got{Some{x}, r2}}
      )
    case _:
      None{}

# the record of a whole payload, or None when it does not decode or bytes
# are left over
def Record.read.end(m: Maybe<&2, Got<Spec.Record>>) -> Maybe<&2, Spec.Record>:
  match m:
    case Some{Got{r, Nil{}}}:
      Some{r}
    case _:
      None{}

# the record of a payload: the tag 0, the line, the content, the node
def Record.read(p: Shared.Bytes()) -> Maybe<&2, Spec.Record>:
  match p:
    case Con{0, b}:
      Record.read.end(
        Got.then(
          String,
          Spec.Record,
          Utf8.read(b),
          ln => r => Got.then(
            Maybe<&2, Shared.Bytes()>,
            Spec.Record,
            Content.read(r),
            c => r2 => Got.then(
              History.Node,
              Spec.Record,
              Node.read(r2),
              v => r3 => Some{Got{Spec.Kept{ln, c, v}, r3}}
            )
          )
        )
      )
    case _:
      None{}

# An entry read whole: its record, and how many bytes it took.
type Entry is Data:
  Entry{record: Spec.Record, size: Nat}

# the entry of a decoded record of size n
def Entry.decoded(m: Maybe<&2, Spec.Record>, n: Nat, r: Shared.Bytes()) -> Maybe<&2, Got<Entry>>:
  match m:
    case None{}:
      None{}
    case Some{rec}:
      Some{Got{Entry{rec, n}, r}}

# the entry of the payload p and the check c, when c is p's check and p
# decodes; n is the size of the whole entry
def Entry.of(
  +p: Shared.Bytes(),
  c: Shared.Bytes(),
  n: Nat,
  r: Shared.Bytes()
) -> Maybe<&2, Got<Entry>>:
  Shared.Bool.when(
    Maybe<&2, Got<Entry>>,
    Shared.Bytes.is_eq(c, Spec.Record.check(p)),
    u => Entry.decoded(Record.read(p), n, r),
    u => None{}
  )

# the entry at the front of b: the length of its payload, the payload, and
# its check, all there and right
def Entry.read(+b: Shared.Bytes()) -> Maybe<&2, Got<Entry>>:
  total = List.length(&2, U32, b)
  Got.then(
    Nat,
    Entry,
    Leb.read(b),
    n => r => Got.then(
      Shared.Bytes(),
      Entry,
      Bytes.read(n, r),
      p => r2 => Got.then(
        Shared.Bytes(),
        Entry,
        Bytes.read(8n, r2),
        c => +r3 => Entry.of(p, c, Nat.sub(total, List.length(&2, U32, r3)), r3)
      )
    )
  )

# the log after the entry m, or the end of the good part when m is None
def Journal.read.next(
  m: Maybe<&2, Got<Entry>>,
  acc: List<&2, Spec.Record>,
  good: Nat,
  k: Shared.Bytes() -> List<&2, Spec.Record> -> Nat -> Spec.Read
) -> Spec.Read:
  match m:
    case None{}:
      Spec.Read{List.reverse(&2, Spec.Record, acc), good}
    case Some{Got{Entry{rec, n}, r}}:
      k(r, rec <> acc, Nat.add(good, n))

# what the log b holds after the records acc (last first) took good bytes;
# fuel bounds the entries (each takes at least one byte)
def Journal.read.go(
  fuel: Nat,
  b: Shared.Bytes(),
  acc: List<&2, Spec.Record>,
  good: Nat
) -> Spec.Read:
  match fuel:
    case 0n:
      Spec.Read{List.reverse(&2, Spec.Record, acc), good}
    case 1n+f:
      Journal.read.next(Entry.read(b), acc, good, r => a2 => g2 => Journal.read.go(f, r, a2, g2))

def Spec.Journal.read(b):
  +b = b
  Journal.read.go(List.length(&2, U32, b), b, [], 0n)
