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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Equality of strings
# -------------------
# Tables compare keys with String.eq, so their laws need it to be
# reflexive and sound.

# Unit when c is not EQ
def Cmp.Ne(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

# no c that is not EQ equals EQ
def Cmp.ne_eq(-c: Cmp, n: Cmp.Ne(c), e: {c == EQ{}: Cmp}) -> Empty:
  %e: Cmp.Ne(_)
  n

# no False equals True
def Bool.false_ne_true(e: {False{} == True{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Cmp.is_eq is True only for EQ
def Cmp.is_eq_sound(c: Cmp) -> {Cmp.is_eq(c) == True{}: Bool} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Bool.false_ne_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Bool.false_ne_true(h))

# Bool.cmp is EQ only for equal Bools
def Bool.cmp_eq(a: Bool, b: Bool) -> {Bool.cmp(a, b) == EQ{}: Cmp} -> {a == b: Bool}:
  match a b:
    case False{} False{}:
      h => {==}
    case False{} True{}:
      h => Empty.absurd({False{} == True{}: Bool}, Cmp.ne_eq(LT{}, Unit{}, h))
    case True{} False{}:
      h => Empty.absurd({True{} == False{}: Bool}, Cmp.ne_eq(GT{}, Unit{}, h))
    case True{} True{}:
      h => {==}

# the last step of Word.cmp_eq, with t the comparison of the tails
def Word.cmp_eq.fin(
  -p: Nat,
  ab: Bool,
  bb: Bool,
  -at: Word(p),
  -bt: Word(p),
  t: Cmp,
  ih: {Word.cmp(p, at, bt) == EQ{}: Cmp} -> {at == bt: Word(p)}
) -> {
  Word.cmp(p, at, bt) == t: Cmp
} -> {Word.cmp.fin(ab, bb, t) == EQ{}: Cmp} -> {WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}:
  match t:
    case LT{}:
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      e => h =>
        %Bool.cmp_eq(ab, bb)(h): {WCon{ab, at} == WCon{_, bt}: Word(1n+p)}
        %ih(e): {WCon{ab, at} == WCon{ab, _}: Word(1n+p)}
        {==}
    case GT{}:
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(GT{}, Unit{}, h))

# Word.cmp is EQ only for equal words
def Word.cmp_eq(
  +n: Nat,
  a: Word(n),
  b: Word(n)
) -> {Word.cmp(n, a, b) == EQ{}: Cmp} -> {a == b: Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          _ => {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          h => Word.cmp_eq.fin(
            p,
            ab,
            bb,
            at,
            bt,
            Word.cmp(p, at, bt),
            Word.cmp_eq(p, at, bt)
          )({==}, h)

# Word.cmp of a word with itself is EQ
def Word.cmp_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{}: Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+np:
      match a:
        case WCon{+head, tail}:
          match head:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(False{}, False{}, _) == EQ{}: Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(True{}, True{}, _) == EQ{}: Cmp}
              {==}

# String.order.go of a string with itself, from EQ, is EQ
def String.order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{}: Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          match x:
            case U32{w}:
              %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, Word.cmp_refl(32n, w)):
                {String.order.go(t, t, _) == EQ{}: Cmp}
              String.order_refl(t)

# String.order.go ends at EQ only if it started at EQ
def String.order_keeps(
  c: Cmp,
  a: String,
  b: String
) -> {String.order.go(a, b, c) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  match c:
    case EQ{}:
      h => {==}
    case LT{}:
      match a b:
        case SNil{} SNil{}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
        case SNil{} SCon{y, t2}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
        case SCon{x, t1} SNil{}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
    case GT{}:
      match a b:
        case SNil{} SNil{}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))
        case SNil{} SCon{y, t2}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))
        case SCon{x, t1} SNil{}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))

# String.order.go from c is String.order.go from EQ, when c is EQ
def String.order_at(
  -c: Cmp,
  -t1: String,
  -t2: String,
  e: {c == EQ{}: Cmp}
) -> {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, EQ{}) == EQ{}: Cmp}:
  %e: {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, _) == EQ{}: Cmp}
  h => h

# String.order.go from EQ ends at EQ only for equal strings
def String.order_sound(
  a: String,
  b: String
) -> {String.order.go(a, b, EQ{}) == EQ{}: Cmp} -> {a == b: String}:
  match a b:
    case SNil{} SNil{}:
      _ => {==}
    case SNil{} SCon{y, t2}:
      h => Empty.absurd({SNil{} == SCon{y, t2}: String}, Cmp.ne_eq(LT{}, Unit{}, h))
    case SCon{x, t1} SNil{}:
      h => Empty.absurd({SCon{x, t1} == SNil{}: String}, Cmp.ne_eq(GT{}, Unit{}, h))
    case SCon{Chr{U32{+w1}}, +t1} SCon{Chr{U32{+w2}}, +t2}:
      +h =>
        +e = String.order_keeps(Word.cmp(32n, w1, w2), t1, t2)(h)
        h2 = String.order_at(Word.cmp(32n, w1, w2), t1, t2, e)(h)
        %Word.cmp_eq(32n, w1, w2)(e): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{_}}, t2}: String}
        %String.order_sound(t1, t2)(h2): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w1}}, _}: String}
        {==}

# every string equals itself
def String.eq_refl(a: String) -> {String.eq(a, a) == True{}: Bool}:
  %Equal.sym(
    Cmp,
    String.order.go(a, a, EQ{}),
    EQ{},
    String.order_refl(a)
  ): {Cmp.is_eq(_) == True{}: Bool}
  {==}

# String.eq is True only for equal strings
def String.eq_sound(
  +a: String,
  +b: String
) -> {String.eq(a, b) == True{}: Bool} -> {a == b: String}:
  h => String.order_sound(a, b)(Cmp.is_eq_sound(String.order.go(a, b, EQ{}))(h))

# String.eq answers False the same way round, with c the answer of
# String.eq(b, a)
def String.eq_flip.at(
  +a: String,
  b: String,
  c: Bool
) -> {String.eq(b, a) == c: Bool} -> {String.eq(a, b) == False{}: Bool} -> {c == False{}: Bool}:
  match c:
    case False{}:
      _ => _ => {==}
    case True{}:
      e => d =>
        ab = Equal.sym(String, b, a, String.eq_sound(b, a)(e))
        same = Equal.cong(String, Bool, z => String.eq(a, z), a, b, ab)
        aa = Equal.sym(Bool, String.eq(a, a), True{}, String.eq_refl(a))
        Equal.trans(
          Bool,
          True{},
          String.eq(a, b),
          False{},
          Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b), aa, same),
          d
        )

# String.eq is False the other way round too
def String.eq_flip(
  +a: String,
  +b: String
) -> {String.eq(a, b) == False{}: Bool} -> {String.eq(b, a) == False{}: Bool}:
  String.eq_flip.at(a, b, String.eq(b, a), {==})

# Tables
# ------
# A table maps keys to values. It is a plain list of rows for now, with no
# key twice; a faster inside (Base's Map, say) may replace it later by
# proving the same three laws. No other spec may rely on anything else
# about a table.

# A table: rows of a key and its value.
type Table<-V: Data> is Data:
  TNil{}
  TRow{key: String, val: V, rest: Table<V>}

# a table with no rows
def Table.new(-V: Data) -> Table<V>:
  TNil{}

# the value of key k in t, or None
def Table.get(-V: Data, t: Table<V>, +k: String) -> Maybe<&2, V>:
  match t:
    case TNil{}:
      None{}
    case TRow{rk, v, r}:
      Bool.when(Maybe<&2, V>, String.eq(rk, k), u => Some{v}, u => Table.get(V, r, k))

# t without the row of key k
def Table.del(-V: Data, t: Table<V>, +k: String) -> Table<V>:
  match t:
    case TNil{}:
      TNil{}
    case TRow{+rk, v, +r}:
      Bool.when(
        Table<V>,
        String.eq(rk, k),
        u => Table.del(V, r, k),
        u => TRow{rk, v, Table.del(V, r, k)}
      )

# t with key k mapped to v
def Table.set(-V: Data, t: Table<V>, +k: String, v: V) -> Table<V>:
  TRow{k, v, Table.del(V, t, k)}

# the keys of t
def Table.keys(-V: Data, t: Table<V>) -> List<&2, String>:
  match t:
    case TNil{}:
      Nil{}
    case TRow{k, v, r}:
      k <> Table.keys(V, r)

# a new table has no value for any key
law Table.get_new:
  for -V: Data
  for k: String
  {Table.get(V, Table.new(V), k) == None{}: Maybe<&2, V>}

def Table.get_new(ty, k):
  {==}

# after setting k to v, k has v
law Table.get_after_set:
  for -V: Data
  for t: Table<V>
  for k: String
  for v: V
  {Table.get(V, Table.set(V, t, k, v), k) == Some{v}: Maybe<&2, V>}

def Table.get_after_set(ty, t, k, v):
  k = k
  %Equal.sym(Bool, String.eq(k, k), True{}, String.eq_refl(k)):
    {
      Bool.when(
        Maybe<&2, ty>,
        _,
        u => Some{v},
        u => Table.get(ty, Table.del(ty, t, k), k)
      )
        == Some{v}: Maybe<&2, ty>
    }
  {==}

# deleting k, with b the answer of String.eq(rk, k) for the first row
def Table.get_del.at(
  -V: Data,
  rk: String,
  v: V,
  -r: Table<V>,
  k: String,
  k2: String,
  b: Bool,
  ih: {Table.get(V, Table.del(V, r, k), k2) == Table.get(V, r, k2): Maybe<&2, V>}
) -> {
  String.eq(rk, k) == b: Bool
} -> {
  String.eq(k, k2) == False{}: Bool
} -> {
  Table.get(
    V,
    Bool.when(Table<V>, b, u => Table.del(V, r, k), u => TRow{rk, v, Table.del(V, r, k)}),
    k2
  )
    == Table.get(V, TRow{rk, v, r}, k2): Maybe<&2, V>
}:
  match b:
    case True{}:
      e => d =>
        %Equal.sym(
          String,
          rk,
          k,
          String.eq_sound(rk, k)(e)
        ): {
          Table.get(
            V,
            Table.del(V, r, k),
            k2
          )
            == Bool.when(
              Maybe<&2, V>,
              String.eq(_, k2),
              u => Some{v},
              u => Table.get(V, r, k2)
            ): Maybe<&2, V>
        }
        %Equal.sym(
          Bool,
          String.eq(k, k2),
          False{},
          d
        ): {
          Table.get(
            V,
            Table.del(V, r, k),
            k2
          )
            == Bool.when(Maybe<&2, V>, _, u => Some{v}, u => Table.get(V, r, k2)): Maybe<&2, V>
        }
        ih
    case False{}:
      e => d =>
        %Equal.sym(Maybe<&2, V>, Table.get(V, Table.del(V, r, k), k2), Table.get(V, r, k2), ih):
          {
            Bool.when(
              Maybe<&2, V>,
              String.eq(rk, k2),
              u => Some{v},
              u => _
            )
              == Table.get(V, TRow{rk, v, r}, k2): Maybe<&2, V>
          }
        {==}

# deleting k keeps the value of every other key
def Table.get_del(
  -V: Data,
  t: Table<V>,
  +k: String,
  +k2: String
) -> {
  String.eq(k, k2) == False{}: Bool
} -> {Table.get(V, Table.del(V, t, k), k2) == Table.get(V, t, k2): Maybe<&2, V>}:
  match t:
    case TNil{}:
      _ => {==}
    case TRow{+rk, v, r}:
      +d => Table.get_del.at(
        V,
        rk,
        v,
        r,
        k,
        k2,
        String.eq(rk, k),
        Table.get_del(V, r, k, k2)(d)
      )({==}, d)

# setting k keeps the value of every other key
law Table.set_keeps_other:
  for -V: Data
  for t: Table<V>
  for k: String
  for v: V
  for k2: String
  for d: {String.eq(k, k2) == False{}: Bool}
  {Table.get(V, Table.set(V, t, k, v), k2) == Table.get(V, t, k2): Maybe<&2, V>}

def Table.set_keeps_other(ty, t, k, v, k2, d):
  k = k
  k2 = k2
  +d = d
  %Equal.sym(Bool, String.eq(k, k2), False{}, d):
    {
      Bool.when(
        Maybe<&2, ty>,
        _,
        u => Some{v},
        u => Table.get(ty, Table.del(ty, t, k), k2)
      )
        == Table.get(ty, t, k2): Maybe<&2, ty>
    }
  Table.get_del(ty, t, k, k2)(d)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
