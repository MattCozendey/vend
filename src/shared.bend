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

# Text
# ----

# A text cut in two at a character: what comes before it, and after it.
type Cut is Data:
  Cut{before: String, after: String}

# the cut of c then a text, given the cut of that text
def Text.cut.on(c: Char, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match r:
    case None{}:
      None{}
    case Some{Cut{b, a}}:
      Some{Cut{SCon{c, b}, a}}

# s cut at its first character with code x, or None when it has none
def Text.cut(s: String, +x: U32) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bool.when(
        Maybe<&2, Cut>,
        U32.is_eq(Char.to_u32(c), x),
        u => Some{Cut{SNil{}, t}},
        u => Text.cut.on(c, Text.cut(t, x))
      )

# s holds a character with code x
def Text.has(s: String, +x: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      List.any.if(u => Text.has(t, x), U32.is_eq(Char.to_u32(c), x))

# URIs
# ----
# A URI in the generic syntax of RFC 3986, section 3, without a query or a
# fragment: scheme ":" ["//" authority] path. The path of a hierarchical
# URI is '/'-separated whatever the scheme, so globs and relative
# references work the same for every scheme.

# A URI: its scheme, its authority when "//" follows the scheme, its path.
type Uri is Data:
  Uri{scheme: String, authority: Maybe<&2, String>, path: String}

# c may go on a scheme after its first letter: a letter, a digit, '+', '-'
# or '.'
def Uri.is_scheme_char(+c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(
    Bool.or(Char.is_alpha(c), Char.is_digit(c)),
    Bool.or(U32.is_eq(x, 43), Bool.or(U32.is_eq(x, 45), U32.is_eq(x, 46)))
  )

# every character of s may go on a scheme
def Uri.scheme_rest(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      List.all.if(u => Uri.scheme_rest(t), Uri.is_scheme_char(c))

# s is a scheme: a letter, then letters, digits, '+', '-' or '.'
def Uri.is_scheme(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      List.all.if(u => Uri.scheme_rest(t), Char.is_alpha(c))

# s holds no '?' (63) and no '#' (35): no query and no fragment
def Uri.plain(+s: String) -> Bool:
  Bool.not(List.any.if(u => Text.has(s, 35), Text.has(s, 63)))

# u is a URI that this module reads and shows: its scheme is a scheme,
# nothing holds a '?' or a '#', an authority holds no '/' and comes before
# an empty path or one that starts with '/', and with no authority the path
# does not start with "//"
def Uri.valid(u: Uri) -> Bool:
  match u:
    case Uri{sc, None{}, +p}:
      List.all.if(
        u => List.all.if(v => Bool.not(String.starts_with(p, "//")), Uri.plain(p)),
        Uri.is_scheme(sc)
      )
    case Uri{+sc, Some{+a}, +p}:
      path_ok = Bool.or(String.is_empty(p), String.starts_with(p, "/"))
      auth_ok = List.all.if(u => Bool.not(Text.has(a, 47)), Uri.plain(a))
      List.all.if(
        u => List.all.if(v => Bool.and(auth_ok, path_ok), Uri.plain(p)),
        Uri.is_scheme(sc)
      )

# the text of u
def Uri.show(u: Uri) -> String:
  match u:
    case Uri{sc, None{}, p}:
      String.append(sc, String.append(":", p))
    case Uri{sc, Some{a}, p}:
      String.append(sc, String.append("://", String.append(a, p)))

# the URI with an authority: up to the first '/', or all of t when it has none
def Uri.read.auth(sc: String, c: Maybe<&2, Cut>, t: String) -> Uri:
  match c:
    case None{}:
      Uri{sc, Some{t}, ""}
    case Some{Cut{a, p}}:
      Uri{sc, Some{a}, SCon{'/', p}}

# the URI of scheme sc and the text t after its ':'
def Uri.read.rest(+sc: String, +t: String) -> Uri:
  Bool.when(
    Uri,
    String.starts_with(t, "//"),
    u => Uri.read.auth(sc, Text.cut(String.drop(t, 2n), 47), String.drop(t, 2n)),
    u => Uri{sc, None{}, t}
  )

# the URI of a cut at the first ':'
def Uri.read.cut(c: Maybe<&2, Cut>) -> Maybe<&2, Uri>:
  match c:
    case None{}:
      None{}
    case Some{Cut{sc, t}}:
      +u = Uri.read.rest(sc, t)
      Bool.when(Maybe<&2, Uri>, Uri.valid(u), v => Some{u}, v => None{})

# the URI of the text t, or None when t is not a valid URI
def Uri.read(t: String) -> Maybe<&2, Uri>:
  Uri.read.cut(Text.cut(t, 58))

# a valid URI reads back from its text
law uri_read_after_show:
  for u: Uri
  for v: {Uri.valid(u) == True{}: Bool}
  {Uri.read(Uri.show(u)) == Some{u}: Maybe<&2, Uri>}

# a read URI shows as the text it came from
law uri_show_after_read:
  for t: String
  for u: Uri
  for h: {Uri.read(t) == Some{u}: Maybe<&2, Uri>}
  {Uri.show(u) == t: String}

# The kinds of endpoint. A mount's URI scheme picks one.
type Endpoint is Data:
  FileEndpoint{}

# the endpoint of u's scheme, or None for a scheme with none yet
def Endpoint.of(u: Uri) -> Maybe<&2, Endpoint>:
  match u:
    case Uri{sc, a, p}:
      Bool.when(Maybe<&2, Endpoint>, String.eq(sc, "file"), v => Some{FileEndpoint{}}, v => None{})

# Names
# -----
# A resource is named by its space and a path relative to the space's root,
# so the same file has the same name on every machine. The path is a valid
# glob-module path (Glob.is_path); this file may import only Base, so the
# places that make names (the core and the views) check it.

# A resource name: the space id, and the path inside the space. Two
# resources are the same exactly when their names are.
type Name is Data:
  Name{space: String, path: String}

# the space of n
def Name.space(n: Name) -> String:
  match n:
    case Name{sp, p}:
      sp

# the path of n
def Name.path(n: Name) -> String:
  match n:
    case Name{sp, p}:
      p

# the text of n: "<space>:<path>"
def Name.show(n: Name) -> String:
  match n:
    case Name{sp, p}:
      String.append(sp, String.append(":", p))

# the name of a cut at the first ':'
def Name.read.cut(c: Maybe<&2, Cut>) -> Maybe<&2, Name>:
  match c:
    case None{}:
      None{}
    case Some{Cut{sp, p}}:
      Some{Name{sp, p}}

# the name of the text t: its space up to the first ':', its path after;
# None when t has no ':'
def Name.read(t: String) -> Maybe<&2, Name>:
  Name.read.cut(Text.cut(t, 58))

# a name whose space holds no ':' reads back from its text
law name_read_after_show:
  for n: Name
  for v: {Text.has(Name.space(n), 58) == False{}: Bool}
  {Name.read(Name.show(n)) == Some{n}: Maybe<&2, Name>}

# a read name shows as the text it came from
law name_show_after_read:
  for t: String
  for n: Name
  for h: {Name.read(t) == Some{n}: Maybe<&2, Name>}
  {Name.show(n) == t: String}
