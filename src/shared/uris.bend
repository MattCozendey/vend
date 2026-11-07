import Base
import ./bools.bend as Bools
import ./texts.bend as Texts

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
  Bool.not(List.any.if(u => Texts.Text.has(s, 35), Texts.Text.has(s, 63)))
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
      auth_ok = List.all.if(u => Bool.not(Texts.Text.has(a, 47)), Uri.plain(a))
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
def Uri.read.auth(sc: String, c: Maybe<&2, Texts.Cut>, t: String) -> Uri:
  match c:
    case None{}:
      Uri{sc, Some{t}, ""}
    case Some{Texts.Cut{a, p}}:
      Uri{sc, Some{a}, SCon{'/', p}}
# the URI of scheme sc and the text t after its ':'
def Uri.read.rest(+sc: String, +t: String) -> Uri:
  Bools.Bool.when(
    Uri,
    String.starts_with(t, "//"),
    u => Uri.read.auth(sc, Texts.Text.cut(String.drop(t, 2n), 47), String.drop(t, 2n)),
    u => Uri{sc, None{}, t}
  )
# the URI of a cut at the first ':'
def Uri.read.cut(c: Maybe<&2, Texts.Cut>) -> Maybe<&2, Uri>:
  match c:
    case None{}:
      None{}
    case Some{Texts.Cut{sc, t}}:
      +u = Uri.read.rest(sc, t)
      Bools.Bool.when(Maybe<&2, Uri>, Uri.valid(u), v => Some{u}, v => None{})
# the URI of the text t, or None when t is not a valid URI
def Uri.read(t: String) -> Maybe<&2, Uri>:
  Uri.read.cut(Texts.Text.cut(t, 58))
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
