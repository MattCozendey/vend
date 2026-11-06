import Base

# a resource's content: one byte per U32, as Base's File effects use
def Bytes() -> Data:
  List<&2, U32>

# x is a byte: below 256
def is_byte(x: U32) -> Bool:
  (x < 256: U32)

# every value of b is a byte
def is_bytes(b: Bytes()) -> Bool:
  List.all(~&2, ~U32, ~is_byte, b)

# a and b are the same bytes
def Bytes.is_eq(a: Bytes(), b: Bytes()) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, at} Con{y, bt}:
      List.all.if(u => Bytes.is_eq(at, bt), U32.is_eq(x, y))
    case _ _:
      False{}

# k(), when b holds, else e(); only the chosen one runs
def Bool.when(-A: Type, b: Bool, k: Unit -> A, e: Unit -> A) -> A:
  match b:
    case False{}:
      e(Unit{})
    case True{}:
      k(Unit{})

# Names
# -----

# The kinds of endpoint, one per scheme.
type Scheme is Data:
  FileScheme{}

# the text of s
def Scheme.show(s: Scheme) -> String:
  match s:
    case FileScheme{}:
      "file"

# every scheme
def Scheme.all() -> List<&2, Scheme>:
  [FileScheme{}]

# A resource name: the scheme, then "://", then the rest, which only the
# endpoint of the scheme reads. Two resources are the same exactly when
# their names are.
type Name is Data:
  Name{scheme: Scheme, rest: String}

# the text of n
def Name.show(n: Name) -> String:
  match n:
    case Name{s, r}:
      String.append(Scheme.show(s), String.append("://", r))

# the name with scheme s, when t, the text after the scheme, starts with "://"
def Name.read.rest(s: Scheme, +t: String) -> Maybe<&2, Name>:
  Bool.when(
    Maybe<&2, Name>,
    String.starts_with(t, "://"),
    u => Some{Name{s, String.drop(t, 3n)}},
    u => None{}
  )

# the name of t, trying each scheme of ss in turn
def Name.read.go(ss: List<&2, Scheme>, +t: String) -> Maybe<&2, Name>:
  match ss:
    case Nil{}:
      None{}
    case Con{+s, r}:
      +k = Scheme.show(s)
      Maybe.or(
        &2,
        Name,
        Bool.when(
          Maybe<&2, Name>,
          String.starts_with(t, k),
          u => Name.read.rest(s, String.drop(t, String.length(k))),
          u => None{}
        ),
        Name.read.go(r, t)
      )

# the name of the text t, or None when t does not start with a known
# scheme then "://"
def Name.read(t: String) -> Maybe<&2, Name>:
  Name.read.go(Scheme.all(), t)

# a shown name reads back
law name_read_after_show:
  for n: Name
  {Name.read(Name.show(n)) == Some{n}: Maybe<&2, Name>}

# a read name shows as the text it came from
law name_show_after_read:
  for t: String
  for n: Name
  for h: {Name.read(t) == Some{n}: Maybe<&2, Name>}
  {Name.show(n) == t: String}
