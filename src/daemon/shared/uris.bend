import Base
import ../../shared.bend as Shared
import ./shared/text.bend as Texts

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
def Uri.is_scheme_rest(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      List.all.if(u => Uri.is_scheme_rest(t), Uri.is_scheme_char(c))
# s is a scheme: a letter, then letters, digits, '+', '-' or '.'
def Uri.is_scheme(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      List.all.if(u => Uri.is_scheme_rest(t), Char.is_alpha(c))
# s holds no '?' (63) and no '#' (35): no query and no fragment
def Uri.is_plain(+s: String) -> Bool:
  Bool.not(List.any.if(u => Texts.Text.has(s, 35), Texts.Text.has(s, 63)))
# u is a URI that this module reads and shows: its scheme is a scheme,
# nothing holds a '?' or a '#', an authority holds no '/' and comes before
# an empty path or one that starts with '/', and with no authority the path
# does not start with "//"
def Uri.is_valid(u: Uri) -> Bool:
  match u:
    case Uri{sc, None{}, +p}:
      List.all.if(
        u => List.all.if(v => Bool.not(String.starts_with(p, "//")), Uri.is_plain(p)),
        Uri.is_scheme(sc)
      )
    case Uri{+sc, Some{+a}, +p}:
      path_ok = Bool.or(String.is_empty(p), String.starts_with(p, "/"))
      auth_ok = List.all.if(u => Bool.not(Texts.Text.has(a, 47)), Uri.is_plain(a))
      List.all.if(
        u => List.all.if(v => Bool.and(auth_ok, path_ok), Uri.is_plain(p)),
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
def Uri.read.auth(sc: String, c: Maybe<&2, Texts.Cut<String>>, t: String) -> Uri:
  match c:
    case None{}:
      Uri{sc, Some{t}, ""}
    case Some{Texts.Cut{a, p}}:
      Uri{sc, Some{a}, SCon{'/', p}}
# the URI of scheme sc and the text t after its ':'
def Uri.read.rest(+sc: String, +t: String) -> Uri:
  Shared.Bool.when(
    Uri,
    String.starts_with(t, "//"),
    u => Uri.read.auth(sc, Texts.Text.cut(String.drop(t, 2n), 47), String.drop(t, 2n)),
    u => Uri{sc, None{}, t}
  )
# the URI of a cut at the first ':'
def Uri.read.cut(c: Maybe<&2, Texts.Cut<String>>) -> Maybe<&2, Uri>:
  match c:
    case None{}:
      None{}
    case Some{Texts.Cut{sc, t}}:
      +u = Uri.read.rest(sc, t)
      Shared.Bool.when(Maybe<&2, Uri>, Uri.is_valid(u), v => Some{u}, v => None{})
# the URI of the text t, or None when t is not a valid URI
def Uri.read(t: String) -> Maybe<&2, Uri>:
  Uri.read.cut(Texts.Text.cut(t, 58))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a scheme character is not ':'
law char_not_colon.at:
  for hit: Bool
  for c: Char
  {
    U32.is_eq(Char.to_u32(c), 58) == hit: Bool
  } -> {Uri.is_scheme_char(c) == True{}: Bool} -> {hit == False{}: Bool}

def char_not_colon.at(hit, c):
  match hit c:
    case True{} Chr{y}:
      e => h =>
        Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true((
              %Shared.U32.is_eq_sound(y, 58)(e): {Uri.is_scheme_char(Chr{_}) == True{}: Bool}
              h)))
    case False{} d:
      e => h => {==}

law char_not_colon:
  for c: Char
  {Uri.is_scheme_char(c) == True{}: Bool} -> {U32.is_eq(Char.to_u32(c), 58) == False{}: Bool}

def char_not_colon(c):
  +c = c
  char_not_colon.at(U32.is_eq(Char.to_u32(c), 58), c)({==})

# a letter is a scheme character
law alpha_scheme:
  for c: Char
  {Char.is_alpha(c) == True{}: Bool} -> {Uri.is_scheme_char(c) == True{}: Bool}

def alpha_scheme(c):
  +h =>
    +c = c
    %Equal.sym(
      Bool,
      Char.is_alpha(c),
      True{},
      h
    ): {
      Bool.or(
        Bool.or(_, Char.is_digit(c)),
        Bool.or(
          U32.is_eq(Char.to_u32(c), 43),
          Bool.or(U32.is_eq(Char.to_u32(c), 45), U32.is_eq(Char.to_u32(c), 46))
        )
      )
        == True{}: Bool
    }
    {==}

# scheme characters hold no ':'
law rest_no_colon:
  for t: String
  {Uri.is_scheme_rest(t) == True{}: Bool} -> {Texts.Text.has(t, 58) == False{}: Bool}

def rest_no_colon(t):
  match t:
    case SNil{}:
      h => {==}
    case SCon{+c, +r}:
      +h =>
        %Equal.sym(
          Bool,
          U32.is_eq(Char.to_u32(c), 58),
          False{},
          char_not_colon(
            c
          )(Shared.List.all.if_hit(Uri.is_scheme_char(c), u => Uri.is_scheme_rest(r))(h))
        ): {List.any.if(u => Texts.Text.has(r, 58), _) == False{}: Bool}
        rest_no_colon(
          r
        )(Shared.List.all.if_rest(Uri.is_scheme_char(c), u => Uri.is_scheme_rest(r))(h))

# a scheme holds no ':'
law scheme_no_colon:
  for t: String
  {Uri.is_scheme(t) == True{}: Bool} -> {Texts.Text.has(t, 58) == False{}: Bool}

def scheme_no_colon(t):
  match t:
    case SNil{}:
      h => Empty.absurd({Texts.Text.has(SNil{}, 58) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case SCon{+c, +r}:
      +h =>
        %Equal.sym(
          Bool,
          U32.is_eq(Char.to_u32(c), 58),
          False{},
          char_not_colon(
            c
          )(
            alpha_scheme(c)(Shared.List.all.if_hit(Char.is_alpha(c), u => Uri.is_scheme_rest(r))(h))
          )
        ): {List.any.if(u => Texts.Text.has(r, 58), _) == False{}: Bool}
        rest_no_colon(r)(Shared.List.all.if_rest(Char.is_alpha(c), u => Uri.is_scheme_rest(r))(h))

# a character that is '/' is '/'
law slash_head:
  for c: Char
  for t: String
  {Char.is_eq(c, '/') == True{}: Bool} -> {SCon{c, t} == SCon{'/', t}: String}

def slash_head(c, t):
  match c:
    case Chr{y}:
      e =>
        +t = t
        Equal.cong(U32, String, z => SCon{Chr{z}, t}, y, 47, Shared.U32.is_eq_sound(y, 47)(e))

# slash_cons, by whether the first character is '/' (b)
law slash_cons.at:
  for b: Bool
  for c: Char
  for t: String
  {
    Char.is_eq(c, '/') == b: Bool
  } -> {String.starts_with.go.if("", t, b) == True{}: Bool} -> {SCon{c, t} == SCon{'/', t}: String}

def slash_cons.at(b, c, t):
  match b:
    case True{}:
      e => h => slash_head(c, t)(e)
    case False{}:
      e => h => Empty.absurd({SCon{c, t} == SCon{'/', t}: String}, Shared.Bool.false_ne_true(h))

# a text that starts with '/' starts with '/'
law slash_cons:
  for c: Char
  for t: String
  {String.starts_with(SCon{c, t}, "/") == True{}: Bool} -> {SCon{c, t} == SCon{'/', t}: String}

def slash_cons(c, t):
  +c = c
  slash_cons.at(Char.is_eq(c, '/'), c, t)({==})

# slash1, by whether the first character is '/' (b)
law slash1.at:
  for b: Bool
  for c: Char
  for r: String
  {
    Char.is_eq(c, '/') == b: Bool
  } -> {
    String.starts_with.go.if("", r, b) == True{}: Bool
  } -> {SCon{c, r} == SCon{'/', String.drop(SCon{c, r}, 1n)}: String}

def slash1.at(b, c, r):
  +r = r
  x => x1 => (%Equal.sym(
    String,
    String.drop(r, 0n),
    r,
    Texts.Text.drop_none(r)
  ): {SCon{c, r} == SCon{'/', _}: String}; slash_cons.at(b, c, r)(x)(x1))

# a text that starts with '/' is '/' then the rest
law slash1:
  for t: String
  {String.starts_with.go("/", t) == True{}: Bool} -> {t == SCon{'/', String.drop(t, 1n)}: String}

def slash1(t):
  match t:
    case SNil{}:
      h => Empty.absurd(
        {SNil{} == SCon{'/', String.drop(SNil{}, 1n)}: String},
        Shared.Bool.false_ne_true(h)
      )
    case SCon{+c, r}:
      slash1.at(Char.is_eq(c, '/'), c, r)({==})

# slash2, by whether the first character is '/' (b)
law slash2.at:
  for b: Bool
  for c: Char
  for r: String
  {
    Char.is_eq(c, '/') == b: Bool
  } -> {
    String.starts_with.go.if("/", r, b) == True{}: Bool
  } -> {SCon{c, r} == String.append("//", String.drop(SCon{c, r}, 2n)): String}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def slash2.at.g11(
  c: Char,
  +head: Char,
  +tail: String,
  x: {Char.is_eq(c, '/') == True{}: Bool},
  x2: Bool,
  hx2: {x2 == Char.is_eq(head, '/'): Bool},
  x1: {String.starts_with.go.if("", tail, x2) == True{}: Bool}
) -> {
  SCon{
    c,
    SCon{head, tail}
  }
    == String.append("//", String.drop(SCon{c, SCon{head, tail}}, 2n)): String
}:
  %slash1.at(x2, head, tail)(Equal.sym(Bool, x2, Char.is_eq(head, '/'), hx2))(x1):
    {SCon{c, SCon{head, tail}} == SCon{'/', _}: String}
  slash_head(c, SCon{head, tail})(x)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def slash2.at(b, c, r):
  match b:
    case False{}:
      x => x1 => Empty.absurd(
        {SCon{c, r} == String.append("//", String.drop(SCon{c, r}, 2n)): String},
        {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
      )
    case True{}:
      match r:
        case SNil{}:
          x => x1 => Empty.absurd(
            {SCon{c, ""} == String.append("//", String.drop(SCon{c, ""}, 2n)): String},
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case SCon{+head, tail}:
          x => x1 => slash2.at.g11(c, head, tail, x, Char.is_eq(head, '/'), {==}, x1)

# a text that starts with "//" is "//" then the rest
law slash2:
  for t: String
  {
    String.starts_with(t, "//") == True{}: Bool
  } -> {t == String.append("//", String.drop(t, 2n)): String}

def slash2(t):
  match t:
    case SNil{}:
      h => Empty.absurd(
        {SNil{} == String.append("//", String.drop(SNil{}, 2n)): String},
        Shared.Bool.false_ne_true(h)
      )
    case SCon{+c, r}:
      slash2.at(Char.is_eq(c, '/'), c, r)({==})

# the authority part of a URI read back: an authority without '/', then an
# empty path or one that starts with '/'
law auth_back:
  for sc: String
  for a: String
  for p: String
  {
    Texts.Text.has(a, 47) == False{}: Bool
  } -> {
    Bool.or(String.is_empty(p), String.starts_with(p, "/")) == True{}: Bool
  } -> {
    Uri.read.auth(
      sc,
      Texts.Text.cut(String.append(a, p), 47),
      String.append(a, p)
    )
      == Uri{sc, Some{a}, p}: Uri
  }

def auth_back(sc, a, p):
  match p:
    case SNil{}:
      +ha => hp =>
        +sc = sc
        +a = a
        %Equal.sym(
          String,
          String.append(a, ""),
          a,
          Texts.Text.append_none(a)
        ): {Uri.read.auth(sc, Texts.Text.cut(_, 47), _) == Uri{sc, Some{a}, ""}: Uri}
        %Equal.sym(
          Maybe<&2, Texts.Cut<String>>,
          Texts.Text.cut(a, 47),
          None{},
          Texts.Text.cut_none(a, 47)(ha)
        ): {Uri.read.auth(sc, _, a) == Uri{sc, Some{a}, ""}: Uri}
        {==}
    case SCon{c, +q}:
      +ha => hp =>
        +sc = sc
        +a = a
        %Equal.sym(
          String,
          SCon{c, q},
          SCon{'/', q},
          slash_cons(c, q)(hp)
        ): {
          Uri.read.auth(
            sc,
            Texts.Text.cut(String.append(a, _), 47),
            String.append(a, _)
          )
            == Uri{sc, Some{a}, _}: Uri
        }
        %Equal.sym(
          Maybe<&2, Texts.Cut<String>>,
          Texts.Text.cut(String.append(a, SCon{'/', q}), 47),
          Some{Texts.Cut{a, q}},
          Texts.Text.cut_at(a, '/', q, 47)(ha)({==})
        ): {
          Uri.read.auth(
            sc,
            _,
            String.append(a, SCon{'/', q})
          )
            == Uri{sc, Some{a}, SCon{'/', q}}: Uri
        }
        {==}

# the URI after a ':' is the one that read.rest reads, when it is valid
law read_cut_of:
  for sc: String
  for rest: String
  for u: Uri
  {
    Uri.read.rest(sc, rest) == u: Uri
  } -> {
    Uri.is_valid(u) == True{}: Bool
  } -> {Uri.read.cut(Some{Texts.Cut{sc, rest}}) == Some{u}: Maybe<&2, Uri>}

def read_cut_of(sc, rest, u):
  e => v =>
    +u = u
    %Equal.sym(
      Uri,
      Uri.read.rest(sc, rest),
      u,
      e
    ): {
      Shared.Bool.when(
        Maybe<&2, Uri>,
        Uri.is_valid(_),
        w => Some{_},
        w => None{}
      )
        == Some{u}: Maybe<&2, Uri>
    }
    %Equal.sym(
      Bool,
      Uri.is_valid(u),
      True{},
      v
    ): {Shared.Bool.when(Maybe<&2, Uri>, _, w => Some{u}, w => None{}) == Some{u}: Maybe<&2, Uri>}
    {==}

# the text of a scheme sc, ':' and rest reads at that ':'
law read_at:
  for sc: String
  for rest: String
  {
    Texts.Text.has(sc, 58) == False{}: Bool
  } -> {
    Uri.read(
      String.append(sc, SCon{':', rest})
    )
      == Uri.read.cut(Some{Texts.Cut{sc, rest}}): Maybe<&2, Uri>
  }

def read_at(sc, rest):
  h =>
    +sc = sc
    +rest = rest
    Equal.cong(
      Maybe<&2, Texts.Cut<String>>,
      Maybe<&2, Uri>,
      z => Uri.read.cut(z),
      Texts.Text.cut(String.append(sc, SCon{':', rest}), 58),
      Some{Texts.Cut{sc, rest}},
      Texts.Text.cut_at(sc, ':', rest, 58)(h)({==})
    )

# an authority read back shows as "//" and its text: by its cut at '/' (m)
law auth_show:
  for m: Maybe<&2, Texts.Cut<String>>
  for sc: String
  for r2: String
  {
    Texts.Text.cut(r2, 47) == m: Maybe<&2, Texts.Cut<String>>
  } -> {
    Uri.show(
      Uri.read.auth(sc, m, r2)
    )
      == String.append(sc, SCon{':', String.append("//", r2)}): String
  }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def auth_show.g1(
  +m: Maybe<&2, Texts.Cut<String>>,
  sc: String,
  r2: String,
  x: {Texts.Text.cut(r2, 47) == m: Maybe<&2, Texts.Cut<String>>}
) -> {
  Uri.show(
    Uri.read.auth(sc, m, r2)
  )
    == String.append(sc, SCon{':', String.append("//", r2)}): String
}:
  match m:
    case None{}:
      %Equal.sym(String, String.append(r2, ""), r2, Texts.Text.append_none(r2)):
        {
          String.append(
            sc,
            SCon{':', SCon{'/', SCon{'/', _}}}
          )
            == String.append(sc, SCon{':', SCon{'/', SCon{'/', r2}}}): String
        }
      {==}
    case Some{value}:
      match value:
        case Texts.Cut{before, after}:
          %Texts.Text.cut_parts(r2, 47, before, after)(x):
            {
              String.append(
                sc,
                SCon{':', SCon{'/', SCon{'/', _}}}
              )
                == String.append(sc, SCon{':', SCon{'/', SCon{'/', r2}}}): String
            }
          {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def auth_show(m, sc, r2):
  x => auth_show.g1(m, sc, r2, x)

# the URI read after a ':' shows as that text: by whether it starts with "//"
# (b)
law rest_show.at:
  for b: Bool
  for sc: String
  for rest: String
  {
    String.starts_with(rest, "//") == b: Bool
  } -> {
    Uri.show(
      Shared.Bool.when(
        Uri,
        b,
        w => Uri.read.auth(sc, Texts.Text.cut(String.drop(rest, 2n), 47), String.drop(rest, 2n)),
        w => Uri{sc, None{}, rest}
      )
    )
      == String.append(sc, SCon{':', rest}): String
  }

def rest_show.at(b, sc, rest):
  match b:
    case False{}:
      x => {==}
    case True{}:
      +rest = rest
      x => (%Equal.sym(
        String,
        Uri.show(
          Uri.read.auth(sc, Texts.Text.cut(String.drop(rest, 2n), 47), String.drop(rest, 2n))
        ),
        String.append(sc, SCon{':', String.append("//", String.drop(rest, 2n))}),
        auth_show(Texts.Text.cut(String.drop(rest, 2n), 47), sc, String.drop(rest, 2n))({==})
      ): {
        _ == String.append(sc, SCon{':', rest}): String
      }; (%slash2(
        rest
      )(x): {String.append(sc, SCon{':', _}) == String.append(sc, SCon{':', rest}): String}; {==}))

law rest_show:
  for sc: String
  for rest: String
  {Uri.show(Uri.read.rest(sc, rest)) == String.append(sc, SCon{':', rest}): String}

def rest_show(sc, rest):
  +rest = rest
  rest_show.at(String.starts_with(rest, "//"), sc, rest)({==})

# a valid URI reads back from its text
law uri_read_after_show:
  for u: Uri
  for v: {Uri.is_valid(u) == True{}: Bool}
  {Uri.read(Uri.show(u)) == Some{u}: Maybe<&2, Uri>}

def uri_read_after_show(u, v):
  match u:
    case Uri{+sc, None{}, +p}:
      +startswith1 = String.starts_with(p, "//")
      +v = v
      hsc = Shared.List.all.if_hit(
        Uri.is_scheme(sc),
        w => List.all.if(x => Bool.not(startswith1), Uri.is_plain(p))
      )(v)
      hns = Shared.Bool.not_true(
        startswith1
      )(
        Shared.List.all.if_rest(
          Uri.is_plain(p),
          x => Bool.not(startswith1)
        )(
          Shared.List.all.if_rest(
            Uri.is_scheme(sc),
            w => List.all.if(x => Bool.not(startswith1), Uri.is_plain(p))
          )(v)
        )
      )
      Equal.trans(
        Maybe<&2, Uri>,
        Uri.read(String.append(sc, SCon{':', p})),
        Uri.read.cut(Some{Texts.Cut{sc, p}}),
        Some{Uri{sc, None{}, p}},
        read_at(sc, p)(scheme_no_colon(sc)(hsc)),
        read_cut_of(sc, p, Uri{sc, None{}, p})((
            %Equal.sym(Bool, startswith1, False{}, hns): {Shared.Bool.when(Uri, _, w => Uri.read.auth(sc, Texts.Text.cut(String.drop(p, 2n), 47), String.drop(p, 2n)), w => Uri{sc, None{}, p}) == Uri{sc, None{}, p}: Uri}
            {==}))(v)
      )
    case Uri{+sc, Some{+a}, +p}:
      +has1 = Texts.Text.has(a, 47)
      +or1 = Bool.or(String.is_empty(p), String.starts_with(p, "/"))
      +not1 = Bool.not(has1)
      +append1 = String.append("//", String.append(a, p))
      +v = v
      hsc = Shared.List.all.if_hit(
        Uri.is_scheme(sc),
        w => List.all.if(
          x => Bool.and(List.all.if(w => not1, Uri.is_plain(a)), or1),
          Uri.is_plain(p)
        )
      )(v)
      +h3 = Shared.List.all.if_rest(
        Uri.is_plain(p),
        x => Bool.and(List.all.if(w => not1, Uri.is_plain(a)), or1)
      )(
        Shared.List.all.if_rest(
          Uri.is_scheme(sc),
          w => List.all.if(
            x => Bool.and(List.all.if(w => not1, Uri.is_plain(a)), or1),
            Uri.is_plain(p)
          )
        )(v)
      )
      ha = Shared.Bool.not_true(
        has1
      )(
        Shared.List.all.if_rest(
          Uri.is_plain(a),
          w => not1
        )(Shared.Bool.and_true_left(List.all.if(w => not1, Uri.is_plain(a)), or1)(h3))
      )
      hp = Shared.Bool.and_true_right(List.all.if(w => not1, Uri.is_plain(a)), or1)(h3)
      Equal.trans(
        Maybe<&2, Uri>,
        Uri.read(String.append(sc, SCon{':', append1})),
        Uri.read.cut(Some{Texts.Cut{sc, append1}}),
        Some{Uri{sc, Some{a}, p}},
        read_at(sc, append1)(scheme_no_colon(sc)(hsc)),
        read_cut_of(sc, append1, Uri{sc, Some{a}, p})((
            %Equal.sym(String, String.drop(String.append(a, p), 0n), String.append(a, p), Texts.Text.drop_none(String.append(a, p))): {Uri.read.auth(sc, Texts.Text.cut(_, 47), _) == Uri{sc, Some{a}, p}: Uri}
            auth_back(sc, a, p)(ha)(hp)))(v)
      )

# show_read once the cut is found: by whether the URI read is valid (b)
law show_read.valid:
  for b: Bool
  for sc: String
  for rest: String
  for u: Uri
  for t: String
  {
    Uri.is_valid(Uri.read.rest(sc, rest)) == b: Bool
  } -> {
    Shared.Bool.when(
      Maybe<&2, Uri>,
      b,
      w => Some{Uri.read.rest(sc, rest)},
      w => None{}
    )
      == Some{u}: Maybe<&2, Uri>
  } -> {t == String.append(sc, SCon{Chr{58}, rest}): String} -> {Uri.show(u) == t: String}

def show_read.valid(b, sc, rest, u, t):
  match b:
    case True{}:
      e => h => ht =>
        +sc = sc
        +rest = rest
        +u = u
        +t = t
        Equal.trans(String, Uri.show(u), String.append(sc, SCon{':', rest}), t, (
            %Equal.cong(Maybe<&2, Uri>, Uri, z => Maybe.default(&2, Uri, z, u), Some{Uri.read.rest(sc, rest)}, Some{u}, h): {Uri.show(_) == String.append(sc, SCon{':', rest}): String}
            rest_show(sc, rest)), Equal.sym(String, t, String.append(sc, SCon{':', rest}), ht))
    case False{}:
      e => h => ht => Empty.absurd(
        {Uri.show(u) == t: String},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Uri>, Bool, z => Maybe.is_some(&2, Uri, z), None{}, Some{u}, h)
        )
      )

# show_read, by whether the text holds a ':' (m is its cut there)
law show_read.at:
  for m: Maybe<&2, Texts.Cut<String>>
  for t: String
  for u: Uri
  {
    Texts.Text.cut(t, 58) == m: Maybe<&2, Texts.Cut<String>>
  } -> {Uri.read.cut(m) == Some{u}: Maybe<&2, Uri>} -> {Uri.show(u) == t: String}

def show_read.at(m, t, u):
  match m:
    case None{}:
      e => h => Empty.absurd(
        {Uri.show(u) == t: String},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Uri>, Bool, z => Maybe.is_some(&2, Uri, z), None{}, Some{u}, h)
        )
      )
    case Some{Texts.Cut{+sc, +rest}}:
      +e => h =>
        +t = t
        +u = u
        show_read.valid(
          Uri.is_valid(Uri.read.rest(sc, rest)),
          sc,
          rest,
          u,
          t
        )({==})(h)(Texts.Text.cut_parts(t, 58, sc, rest)(e))

# a read URI shows as the text it came from
law uri_show_after_read:
  for t: String
  for u: Uri
  for h: {Uri.read(t) == Some{u}: Maybe<&2, Uri>}
  {Uri.show(u) == t: String}

def uri_show_after_read(t, u, h):
  +t = t
  show_read.at(Texts.Text.cut(t, 58), t, u)({==})(h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Endpoints
# ---------

# The kinds of endpoint. A mount's URI scheme picks one.
type Endpoint is Data:
  file_endpoint{}
