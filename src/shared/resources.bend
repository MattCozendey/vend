import Base
import ./shared.bend as Shared
import ./text.bend as Texts

# Names
# -----
# A resource is named by its space and a path relative to the space's root,
# so the same file has the same name on every machine. The path is a valid
# glob-module path (Glob.is_path); a shared module may import only
# shared.bend, so the places that make names (the core and the views) check
# it.

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
def Name.is_eq(a: Name, b: Name) -> Bool:
  String.eq(Name.show(a), Name.show(b))

# Name.is_eq is True for a name and itself
def Name.is_eq_refl(a: Name) -> {Name.is_eq(a, a) == True{}: Bool}:
  match a:
    case Name{t}:
      Texts.String.eq_refl(t)

# Name.is_eq is True only for equal names
def Name.is_eq_sound(a: Name, b: Name) -> {Name.is_eq(a, b) == True{}: Bool} -> {a == b: Name}:
  match a b:
    case Name{x} Name{y}:
      h =>
        %Texts.String.eq_sound(x, y)(h): {Name{x} == Name{_}: Name}
        {==}

# the laws of Name.is_eq
def Name.laws() -> Shared.Eq.Laws(Name, Name.is_eq):
  (Name.is_eq_refl, Name.is_eq_sound)
# the space in the cut c of the text t: t itself when it has no ':'
def Name.space.cut(c: Maybe<&2, Texts.Cut<String>>, t: String) -> String:
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
def Name.path.cut(c: Maybe<&2, Texts.Cut<String>>) -> String:
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
  Shared.Bool.when(Maybe<&2, Name>, Texts.Text.has(t, 58), u => Some{Name{t}}, u => None{})
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
        Shared.Bool.when(
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
    Shared.Bool.when(
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

# Paths
# -----
# A resource names another by a path from its own folder: "." stays, ".."
# goes up one folder, and a path that starts with '/' starts at the root of
# the space.

# the folders done (the last first) after the part p
def Path.step(+p: String, +done: List<&2, String>) -> List<&2, String>:
  Shared.Bool.when(
    List<&2, String>,
    String.eq(p, ".."),
    u => List.tail(&2, String, done),
    u => Shared.Bool.when(
      List<&2, String>,
      Bool.or(String.eq(p, "."), String.is_empty(p)),
      v => done,
      v => p <> done
    )
  )

# the parts of a path after the parts ps, from the folders done (the last
# first)
def Path.walk(ps: List<&2, String>, done: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      List.reverse(&2, String, done)
    case Con{p, r}:
      Path.walk(r, Path.step(p, done))

# the parts of the path t, after the folder parts fs when t does not start
# with '/'
def Path.parts(fs: List<&2, String>, +t: String) -> List<&2, String>:
  Shared.Bool.when(
    List<&2, String>,
    String.starts_with(t, "/"),
    u => String.split(t, Chr{47}),
    u => List.append(&2, String, fs, String.split(t, Chr{47}))
  )

# the resource at the path t from the folder of the resource n
def Name.at(+n: Name, t: String) -> Name:
  ps = String.split(Name.path(n), Chr{47})
  fs = List.reverse(&2, String, List.tail(&2, String, List.reverse(&2, String, ps)))
  Name{
    String.append(
      Name.space(n),
      String.append(":", String.join(Path.walk(Path.parts(fs, t), []), "/"))
    )
  }
