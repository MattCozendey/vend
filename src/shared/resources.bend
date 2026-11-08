import Base
import ./bools.bend as Bools
import ./shared.bend as Shared
import ./strings.bend as Strings
import ./texts.bend as Texts
import ./uris.bend as Uris

# Names
# -----
# A resource is named by its space and a path relative to the space's root,
# so the same file has the same name on every machine. The path is a valid
# glob-module path (Glob.is_path); this file may import only Base, so the
# places that make names (the core and the views) check it.

# A resource name is its text, "<space>:<path>": the space is the text up to
# its first ':', the path is the rest. Two resources are the same exactly when
# their names are, and two names are one name exactly when their texts are.
type Name is Data:
  Name{text: String}
# the text of n
def Name.show(n: Name) -> String:
  match n:
    case Name{t}:
      t
# a and b are the same resource
def Name.same(a: Name, b: Name) -> Bool:
  String.eq(Name.show(a), Name.show(b))

# Name.same is True for a name and itself
def Name.same_refl(a: Name) -> {Name.same(a, a) == True{}: Bool}:
  match a:
    case Name{t}:
      Strings.String.eq_refl(t)

# Name.same is True only for equal names
def Name.same_sound(a: Name, b: Name) -> {Name.same(a, b) == True{}: Bool} -> {a == b: Name}:
  match a b:
    case Name{x} Name{y}:
      h =>
        %Strings.String.eq_sound(x, y)(h): {Name{x} == Name{_}: Name}
        {==}

# the space in the cut c of the text t: t itself when it has no ':'
def Name.space.cut(c: Maybe<&2, Texts.Cut>, t: String) -> String:
  match c:
    case None{}:
      t
    case Some{Texts.Cut{sp, p}}:
      sp
# the space of n
def Name.space(n: Name) -> String:
  match n:
    case Name{+t}:
      Name.space.cut(Texts.Text.cut(t, 58), t)
# the path in the cut c: none when the text has no ':'
def Name.path.cut(c: Maybe<&2, Texts.Cut>) -> String:
  match c:
    case None{}:
      ""
    case Some{Texts.Cut{sp, p}}:
      p
# the path of n
def Name.path(n: Name) -> String:
  match n:
    case Name{t}:
      Name.path.cut(Texts.Text.cut(t, 58))
# the name of the text t; None when t has no ':'
def Name.read(+t: String) -> Maybe<&2, Name>:
  Bools.Bool.when(Maybe<&2, Name>, Texts.Text.has(t, 58), u => Some{Name{t}}, u => None{})
# a name whose text holds a ':' reads back from its text
law name_read_after_show:
  for n: Name
  for v: {Texts.Text.has(Name.show(n), 58) == True{}: Bool}
  {Name.read(Name.show(n)) == Some{n}: Maybe<&2, Name>}

def name_read_after_show(n, v):
  match n:
    case Name{t}:
      %Equal.sym(
        Bool,
        Texts.Text.has(t, 58),
        True{},
        v
      ): {
        Bools.Bool.when(
          Maybe<&2, Name>,
          _,
          u => Some{Name{t}},
          u => None{}
        )
          == Some{Name{t}}: Maybe<&2, Name>
      }
      {==}

# name_show_after_read, by whether t holds a ':' (hit)
law name_show_after_read.at:
  for hit: Bool
  for t: String
  for n: Name
  {
    Texts.Text.has(t, 58) == hit: Bool
  } -> {
    Bools.Bool.when(
      Maybe<&2, Name>,
      hit,
      u => Some{Name{t}},
      u => None{}
    )
      == Some{n}: Maybe<&2, Name>
  } -> {Name.show(n) == t: String}

def name_show_after_read.at(hit, t, n):
  match hit:
    case True{}:
      e => h =>
        +n = n
        +t = t
        Equal.sym(
          String,
          t,
          Name.show(n),
          Equal.cong(
            Maybe<&2, Name>,
            String,
            z => Name.show(Maybe.default(&2, Name, z, Name{""})),
            Some{Name{t}},
            Some{n},
            h
          )
        )
    case False{}:
      e => h => Empty.absurd(
        {Name.show(n) == t: String},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Name>, Bool, z => Maybe.is_some(&2, Name, z), None{}, Some{n}, h)
        )
      )

# a read name shows as the text it came from
law name_show_after_read:
  for t: String
  for n: Name
  for h: {Name.read(t) == Some{n}: Maybe<&2, Name>}
  {Name.show(n) == t: String}

def name_show_after_read(t, n, h):
  +t = t
  name_show_after_read.at(Texts.Text.has(t, 58), t, n)({==})(h)

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
