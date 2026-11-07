import Base
import ./bools.bend as Bools
import ./texts.bend as Texts
import ./uris.bend as Uris

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
def Name.read.cut(c: Maybe<&2, Texts.Cut>) -> Maybe<&2, Name>:
  match c:
    case None{}:
      None{}
    case Some{Texts.Cut{sp, p}}:
      Some{Name{sp, p}}
# the name of the text t: its space up to the first ':', its path after;
# None when t has no ':'
def Name.read(t: String) -> Maybe<&2, Name>:
  Name.read.cut(Texts.Text.cut(t, 58))
# a name whose space holds no ':' reads back from its text
law name_read_after_show:
  for n: Name
  for v: {Texts.Text.has(Name.space(n), 58) == False{}: Bool}
  {Name.read(Name.show(n)) == Some{n}: Maybe<&2, Name>}
# a read name shows as the text it came from
law name_show_after_read:
  for t: String
  for n: Name
  for h: {Name.read(t) == Some{n}: Maybe<&2, Name>}
  {Name.show(n) == t: String}

# Endpoints
# ---------

# The kinds of endpoint. A mount's URI scheme picks one.
type Endpoint is Data:
  FileEndpoint{}
# the endpoint of u's scheme, or None for a scheme with none yet
def Endpoint.of(u: Uris.Uri) -> Maybe<&2, Endpoint>:
  match u:
    case Uris.Uri{sc, a, p}:
      Bools.Bool.when(
        Maybe<&2, Endpoint>,
        String.eq(sc, "file"),
        v => Some{FileEndpoint{}},
        v => None{}
      )
