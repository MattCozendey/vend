import Base
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/text.bend as Texts
import ../run/files.bend as Run

# Well-formed files
# ----------------
# The files are a plain crit-bit map (run/files.bend). Its laws hold of a map
# that is well formed; the code that runs builds no proof of it.

# the map of the files t is well formed
def Files.wf(t: Run.Files) -> Bool:
  match t:
    case Run.Files{m}:
      Crits.Crit.wf(~Run.Files.Item, m, 0n)

# no file is well formed
def Files.new_wf() -> {Files.wf(Run.Files.new()) == True{}: Bool}:
  Crits.Crit.new_wf(~Run.Files.Item)

# a write keeps the files well formed
def Files.set_wf(
  t: Run.Files,
  +p: String,
  w: Maybe<&2, List<&2, U32>>
) -> {Files.wf(t) == True{}: Bool} -> {Files.wf(Run.Files.set(t, p, w)) == True{}: Bool}:
  match t w:
    case Run.Files{+m} None{}:
      h => Crits.Crit.drop_wf(~Run.Files.Item, m, Run.Files.key(p))(h)
    case Run.Files{+m} Some{+ws}:
      h => Crits.Crit.upsert_wf(
        ~Run.Files.Item,
        ~(a => b => b),
        m,
        Run.Files.key(p),
        Run.Files.Item{p, ws}
      )(h)

# Entries that pass a test
# ------------------------

# some entry of es passes f with g
def Binds.any(
  ~V: Data,
  ~G: Data,
  ~f: G -> Crits.Bind<V> -> Bool,
  es: List<&2, Crits.Bind<V>>,
  +g: G
) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{b, r}:
      List.any.if(u => Binds.any(~V, ~G, ~f, r, g), f(g)(b))

# a choice whose rest holds, holds
def Any.rest(
  hit: Bool,
  -rest: Unit -> Bool
) -> {rest(Unit{}) == True{}: Bool} -> {List.any.if(rest, hit) == True{}: Bool}:
  match hit:
    case False{}:
      h => h
    case True{}:
      h => {==}

# a choice whose head holds, holds
def Any.hit(
  hit: Bool,
  -rest: Unit -> Bool
) -> {hit == True{}: Bool} -> {List.any.if(rest, hit) == True{}: Bool}:
  match hit:
    case False{}:
      h => Empty.absurd({List.any.if(rest, False{}) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case True{}:
      h => {==}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# an entry that passes among rest passes among the entries of m then rest
def Binds.any_rest(
  ~V: Data,
  ~G: Data,
  ~f: G -> Crits.Bind<V> -> Bool,
  m: Crits.Crit<V>,
  +rest: List<&2, Crits.Bind<V>>,
  +g: G
) -> {
  Binds.any(~V, ~G, ~f, rest, g) == True{}: Bool
} -> {Binds.any(~V, ~G, ~f, Crits.Crit.entries.go(V, m, rest), g) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => h
    case Crits.Crit.Leaf{k, v}:
      h => Any.rest(f(g)(Crits.Bind{k, v}), u => Binds.any(~V, ~G, ~f, rest, g))(h)
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      h => Binds.any_rest(
        ~V,
        ~G,
        ~f,
        z,
        Crits.Crit.entries.go(V, o, rest),
        g
      )(Binds.any_rest(~V, ~G, ~f, o, rest, g)(h))
    case Crits.Crit.Fork{r, p, Some{v}, +z, +o}:
      h => Any.rest(
        f(g)(Crits.Bind{r, v}),
        u => Binds.any(
          ~V,
          ~G,
          ~f,
          Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
          g
        )
      )(
        Binds.any_rest(
          ~V,
          ~G,
          ~f,
          z,
          Crits.Crit.entries.go(V, o, rest),
          g
        )(Binds.any_rest(~V, ~G, ~f, o, rest, g)(h))
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# an entry read at the key k that passes, passes at the head
def Binds.any_head(
  ~V: Data,
  ~G: Data,
  ~f: G -> Crits.Bind<V> -> Bool,
  +k2: List<&2, U32>,
  +w: V,
  +k: List<&2, U32>,
  +v: V,
  +g: G,
  -rest: Unit -> Bool,
  +b: Bool
) -> {
  Crits.Key.is_eq(k2, k) == b: Bool
} -> {
  Shared.Maybe.when(V, b, u => Some{w}) == Some{v}: Maybe<&2, V>
} -> {
  f(g)(Crits.Bind{k, v}) == True{}: Bool
} -> {List.any.if(rest, f(g)(Crits.Bind{k2, w})) == True{}: Bool}:
  eb => +hw => hf =>
    %Equal.sym(
      List<&2, U32>,
      k2,
      k,
      Crits.Crit.ws_key(V, k2, w, k, v, b)(eb)(hw)
    ): {List.any.if(rest, f(g)(Crits.Bind{_, w})) == True{}: Bool}
    %Equal.sym(
      V,
      w,
      v,
      Crits.Crit.ws_val(V, w, v, b)(hw)
    ): {List.any.if(rest, f(g)(Crits.Bind{k, _})) == True{}: Bool}
    Any.hit(f(g)(Crits.Bind{k, v}), rest)(hf)

# an entry of m that passes, passes among the entries of m then rest
def Binds.any_hit(
  ~V: Data,
  ~G: Data,
  ~f: G -> Crits.Bind<V> -> Bool,
  m: Crits.Crit<V>,
  +rest: List<&2, Crits.Bind<V>>,
  +g: G,
  +k: List<&2, U32>,
  +v: V
) -> {
  Crits.Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>
} -> {
  f(g)(Crits.Bind{k, v}) == True{}: Bool
} -> {Binds.any(~V, ~G, ~f, Crits.Crit.entries.go(V, m, rest), g) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => hf => Empty.absurd(
        {Binds.any(~V, ~G, ~f, rest, g) == True{}: Bool},
        Shared.Maybe.none_ne_some(V, v, h)
      )
    case Crits.Crit.Leaf{+k2, +w}:
      h => hf => Binds.any_head(
        ~V,
        ~G,
        ~f,
        k2,
        w,
        k,
        v,
        g,
        u => Binds.any(~V, ~G, ~f, rest, g),
        Crits.Key.is_eq(k2, k)
      )({==})(h)(hf)
    case Crits.Crit.Fork{+r, p, None{}, +z, +o}:
      h => +hf => Crits.Crit.or3_some(
        V,
        {
          Binds.any(
            ~V,
            ~G,
            ~f,
            Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
            g
          )
            == True{}: Bool
        },
        Crits.Crit.ended(V, r, None{}, k),
        Crits.Crit.lookup(V, z, k),
        Crits.Crit.lookup(V, o, k),
        v
      )(
        h1 => Empty.absurd(
          {
            Binds.any(
              ~V,
              ~G,
              ~f,
              Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
              g
            )
              == True{}: Bool
          },
          Shared.Maybe.none_ne_some(V, v, h1)
        )
      )(
        h2 => Binds.any_hit(~V, ~G, ~f, z, Crits.Crit.entries.go(V, o, rest), g, k, v)(h2)(hf)
      )(
        h3 => Binds.any_rest(
          ~V,
          ~G,
          ~f,
          z,
          Crits.Crit.entries.go(V, o, rest),
          g
        )(Binds.any_hit(~V, ~G, ~f, o, rest, g, k, v)(h3)(hf))
      )(h)
    case Crits.Crit.Fork{+r, p, Some{+w}, +z, +o}:
      h => +hf => Crits.Crit.or3_some(
        V,
        {
          List.any.if(
            u => Binds.any(
              ~V,
              ~G,
              ~f,
              Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
              g
            ),
            f(g)(Crits.Bind{r, w})
          )
            == True{}: Bool
        },
        Crits.Crit.ended(V, r, Some{w}, k),
        Crits.Crit.lookup(V, z, k),
        Crits.Crit.lookup(V, o, k),
        v
      )(
        h1 => Binds.any_head(
          ~V,
          ~G,
          ~f,
          r,
          w,
          k,
          v,
          g,
          u => Binds.any(
            ~V,
            ~G,
            ~f,
            Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
            g
          ),
          Crits.Key.is_eq(r, k)
        )({==})(h1)(hf)
      )(
        h2 => Any.rest(
          f(g)(Crits.Bind{r, w}),
          u => Binds.any(
            ~V,
            ~G,
            ~f,
            Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
            g
          )
        )(Binds.any_hit(~V, ~G, ~f, z, Crits.Crit.entries.go(V, o, rest), g, k, v)(h2)(hf))
      )(
        h3 => Any.rest(
          f(g)(Crits.Bind{r, w}),
          u => Binds.any(
            ~V,
            ~G,
            ~f,
            Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
            g
          )
        )(
          Binds.any_rest(
            ~V,
            ~G,
            ~f,
            z,
            Crits.Crit.entries.go(V, o, rest),
            g
          )(Binds.any_hit(~V, ~G, ~f, o, rest, g, k, v)(h3)(hf))
        )
      )(h)

# Laws of files
# -------------

# a path that equals another is not unequal to it
def Files.eq_self_false(
  +p: String,
  -q: String,
  e: {p == q: String}
) -> {String.eq(p, q) == False{}: Bool} -> Empty:
  %e: {String.eq(p, _) == False{}: Bool} -> Empty
  h => Shared.Bool.true_ne_false(
    Equal.trans(
      Bool,
      True{},
      String.eq(p, p),
      False{},
      Equal.sym(Bool, String.eq(p, p), True{}, Texts.String.eq_refl(p)),
      h
    )
  )

# the keys of two unequal paths are unequal, when their test is b
def Files.key_ne.at(
  +p: String,
  +q: String,
  b: Bool
) -> {
  Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)) == b: Bool
} -> {String.eq(p, q) == False{}: Bool} -> {b == False{}: Bool}:
  match b:
    case False{}:
      e => h => {==}
    case True{}:
      e => h => Empty.absurd(
        {True{} == False{}: Bool},
        Files.eq_self_false(
          p,
          q,
          Equal.sym(
            String,
            q,
            p,
            Codes.Code.is_eq_sound(
              ~String,
              ~Codes.Code.text,
              ~Codes.Code.text.read,
              ~(x => r => Codes.Code.text_read(x, r)),
              q,
              p
            )(e)
          )
        )(h)
      )

# the keys of two unequal paths are unequal
def Files.key_ne(
  +p: String,
  +q: String
) -> {
  String.eq(p, q) == False{}: Bool
} -> {Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)) == False{}: Bool}:
  h => Files.key_ne.at(p, q, Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)))({==})(h)

# no file holds no path
def Files.get_new(+p: String) -> {Run.Files.get(Run.Files.new(), p) == None{}: Maybe<&2, List<&2, U32>>}:
  {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a write is read back at its path
def Files.get_set_same(
  t: Run.Files,
  +p: String,
  w: Maybe<&2, List<&2, U32>>
) -> {
  Files.wf(t) == True{}: Bool
} -> {Run.Files.get(Run.Files.set(t, p, w), p) == w: Maybe<&2, List<&2, U32>>}:
  match t w:
    case Run.Files{+m} None{}:
      +wf =>
      %Equal.sym(
        Maybe<&2, Run.Files.Item>,
        Crits.Dict.get(Run.Files.Item, Crits.Dict.drop(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p)), Run.Files.key(p)),
        Bool.pick(
          Maybe<&2, Run.Files.Item>,
          Crits.Key.is_eq(Run.Files.key(p), Run.Files.key(p)),
          None{},
          Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(p))
        ),
        Crits.Dict.get_drop(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.key(p))
      ): {Run.Files.get.of(_, p) == None{}: Maybe<&2, List<&2, U32>>}
      %Equal.sym(
        Bool,
        Crits.Key.is_eq(Run.Files.key(p), Run.Files.key(p)),
        True{},
        Crits.Key.is_eq_refl(Run.Files.key(p))
      ): {
        Run.Files.get.of(
          Bool.pick(Maybe<&2, Run.Files.Item>, _, None{}, Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(p))),
          p
        )
          == None{}: Maybe<&2, List<&2, U32>>
      }
      {==}
    case Run.Files{+m} Some{+ws}:
      +wf =>
      %Equal.sym(
        Maybe<&2, Run.Files.Item>,
        Crits.Dict.get(
          Run.Files.Item,
          Crits.Dict.set(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.Item{p, ws}),
          Run.Files.key(p)
        ),
        Bool.pick(
          Maybe<&2, Run.Files.Item>,
          Crits.Key.is_eq(Run.Files.key(p), Run.Files.key(p)),
          Some{Run.Files.Item{p, ws}},
          Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(p))
        ),
        Crits.Dict.get_set(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.Item{p, ws}, Run.Files.key(p))
      ): {Run.Files.get.of(_, p) == Some{ws}: Maybe<&2, List<&2, U32>>}
      %Equal.sym(
        Bool,
        Crits.Key.is_eq(Run.Files.key(p), Run.Files.key(p)),
        True{},
        Crits.Key.is_eq_refl(Run.Files.key(p))
      ): {
        Run.Files.get.of(
          Bool.pick(
            Maybe<&2, Run.Files.Item>,
            _,
            Some{Run.Files.Item{p, ws}},
            Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(p))
          ),
          p
        )
          == Some{ws}: Maybe<&2, List<&2, U32>>
      }
      %Equal.sym(
        Bool,
        String.eq(p, p),
        True{},
        Texts.String.eq_refl(p)
      ): {
        Bool.pick(
          Maybe<&2, List<&2, U32>>,
          _,
          Some{ws},
          None{}
        )
          == Some{ws}: Maybe<&2, List<&2, U32>>
      }
      {==}

# a write changes no other path
def Files.get_set_other(
  t: Run.Files,
  +p: String,
  w: Maybe<&2, List<&2, U32>>,
  +q: String
) -> {
  String.eq(p, q) == False{}: Bool
} -> {
  Files.wf(t) == True{}: Bool
} -> {Run.Files.get(Run.Files.set(t, p, w), q) == Run.Files.get(t, q): Maybe<&2, List<&2, U32>>}:
  match t w:
    case Run.Files{+m} None{}:
      h => +wf =>
        %Equal.sym(
          Maybe<&2, Run.Files.Item>,
          Crits.Dict.get(Run.Files.Item, Crits.Dict.drop(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p)), Run.Files.key(q)),
          Bool.pick(
            Maybe<&2, Run.Files.Item>,
            Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)),
            None{},
            Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q))
          ),
          Crits.Dict.get_drop(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.key(q))
        ): {
          Run.Files.get.of(
            _,
            q
          )
            == Run.Files.get.of(
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q)),
              q
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)),
          False{},
          Files.key_ne(p, q)(h)
        ): {
          Run.Files.get.of(
            Bool.pick(
              Maybe<&2, Run.Files.Item>,
              _,
              None{},
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q))
            ),
            q
          )
            == Run.Files.get.of(
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q)),
              q
            ): Maybe<&2, List<&2, U32>>
        }
        {==}
    case Run.Files{+m} Some{+ws}:
      h => +wf =>
        %Equal.sym(
          Maybe<&2, Run.Files.Item>,
          Crits.Dict.get(
            Run.Files.Item,
            Crits.Dict.set(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.Item{p, ws}),
            Run.Files.key(q)
          ),
          Bool.pick(
            Maybe<&2, Run.Files.Item>,
            Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)),
            Some{Run.Files.Item{p, ws}},
            Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q))
          ),
          Crits.Dict.get_set(~Run.Files.Item, Tuple{m, wf}, Run.Files.key(p), Run.Files.Item{p, ws}, Run.Files.key(q))
        ): {
          Run.Files.get.of(
            _,
            q
          )
            == Run.Files.get.of(
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q)),
              q
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(Run.Files.key(q), Run.Files.key(p)),
          False{},
          Files.key_ne(p, q)(h)
        ): {
          Run.Files.get.of(
            Bool.pick(
              Maybe<&2, Run.Files.Item>,
              _,
              Some{Run.Files.Item{p, ws}},
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q))
            ),
            q
          )
            == Run.Files.get.of(
              Crits.Dict.get(Run.Files.Item, Tuple{m, wf}, Run.Files.key(q)),
              q
            ): Maybe<&2, List<&2, U32>>
        }
        {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the entry b counts, and its path is p
def Files.holds(p: String, b: Crits.Bind<Run.Files.Item>) -> Bool:
  match b:
    case Crits.Bind{k, Run.Files.Item{+q, ws}}:
      Bool.and(Crits.Key.is_eq(k, Run.Files.key(q)), String.eq(q, p))

# the entry of the path p under its key counts
def Files.holds_self(
  +p: String,
  -ws: List<&2, U32>
) -> {Files.holds(p, Crits.Bind{Run.Files.key(p), Run.Files.Item{p, ws}}) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Crits.Key.is_eq(Run.Files.key(p), Run.Files.key(p)),
    True{},
    Crits.Key.is_eq_refl(Run.Files.key(p))
  ): {Bool.and(_, String.eq(p, p)) == True{}: Bool}
  %Equal.sym(
    Bool,
    String.eq(p, p),
    True{},
    Texts.String.eq_refl(p)
  ): {Bool.and(True{}, _) == True{}: Bool}
  {==}

# Files.get.of_some when the test of the paths is b
def Files.get.of_some.at(
  +q: String,
  -ws2: List<&2, U32>,
  +p: String,
  -ws: List<&2, U32>,
  b: Bool
) -> {
  String.eq(q, p) == b: Bool
} -> {
  Bool.pick(Maybe<&2, List<&2, U32>>, b, Some{ws2}, None{}) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {Some{Run.Files.Item{q, ws2}} == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>}:
  match b:
    case True{}:
      e => h =>
        %Equal.sym(
          String,
          q,
          p,
          Texts.String.eq_sound(q, p)(e)
        ): {Some{Run.Files.Item{_, ws2}} == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>}
        %Equal.sym(
          List<&2, U32>,
          ws2,
          ws,
          Shared.Maybe.some_inj(List<&2, U32>, ws2, ws, h)
        ): {Some{Run.Files.Item{p, _}} == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>}
        {==}
    case False{}:
      e => h => Empty.absurd(
        {Some{Run.Files.Item{q, ws2}} == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>},
        Shared.Maybe.none_ne_some(List<&2, U32>, ws, h)
      )

# a file that answers the words ws at the path p is the file of p and ws
def Files.get.of_some(
  m: Maybe<&2, Run.Files.Item>,
  +p: String,
  -ws: List<&2, U32>
) -> {
  Run.Files.get.of(m, p) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {m == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{Run.Files.Item{p, ws}}: Maybe<&2, Run.Files.Item>},
        Shared.Maybe.none_ne_some(List<&2, U32>, ws, h)
      )
    case Some{Run.Files.Item{+q, +ws2}}:
      h => Files.get.of_some.at(q, ws2, p, ws, String.eq(q, p))({==})(h)

# Files.paths_any for a first entry whose key test is a and path test is b
def Files.paths_any.at(
  a: Bool,
  b: Bool,
  +q: String,
  +p: String,
  +rest: List<&2, String>,
  -anyr: Bool
) -> {
  String.eq(q, p) == b: Bool
} -> (
  {anyr == True{}: Bool} -> {List.contains(~String, ~String.eq, rest, p) == True{}: Bool}
) -> {
  List.any.if(u => anyr, Bool.and(a, b)) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Run.Files.paths.if(a, q, rest), p) == True{}: Bool}:
  match a b:
    case True{} True{}:
      e => ih => h => Any.hit(String.eq(q, p), u => List.contains(~String, ~String.eq, rest, p))(e)
    case True{} False{}:
      e => ih => h => Any.rest(
        String.eq(q, p),
        u => List.contains(~String, ~String.eq, rest, p)
      )(ih(h))
    case False{} True{}:
      e => ih => h => ih(h)
    case False{} False{}:
      e => ih => h => ih(h)

# the path of an entry that counts is among the paths
def Files.paths_any(
  es: List<&2, Crits.Bind<Run.Files.Item>>,
  +p: String
) -> {
  Binds.any(~Run.Files.Item, ~String, ~(g => b => Files.holds(g, b)), es, p) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Run.Files.paths.go(es), p) == True{}: Bool}:
  match es:
    case Nil{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{Crits.Bind{+k, Run.Files.Item{+q, ws}}, +r}:
      h => Files.paths_any.at(
        Crits.Key.is_eq(k, Run.Files.key(q)),
        String.eq(q, p),
        q,
        p,
        Run.Files.paths.go(r),
        Binds.any(~Run.Files.Item, ~String, ~(g => b => Files.holds(g, b)), r, p)
      )({==})(Files.paths_any(r, p))(h)

# a path that holds words is among the paths
def Files.get_paths(
  t: Run.Files,
  +p: String,
  +ws: List<&2, U32>
) -> {
  Files.wf(t) == True{}: Bool
} -> {
  Run.Files.get(t, p) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {List.contains(~String, ~String.eq, Run.Files.paths(t), p) == True{}: Bool}:
  match t:
    case Run.Files{+m}:
      +w => h => Files.paths_any(
        Crits.Crit.entries(Run.Files.Item, m),
        p
      )(
        Binds.any_hit(
          ~Run.Files.Item,
          ~String,
          ~(g => b => Files.holds(g, b)),
          m,
          [],
          p,
          Run.Files.key(p),
          Run.Files.Item{p, ws}
        )(
          Equal.trans(
            Maybe<&2, Run.Files.Item>,
            Crits.Crit.lookup(Run.Files.Item, m, Run.Files.key(p)),
            Crits.Crit.get(Run.Files.Item, m, Run.Files.key(p)),
            Some{Run.Files.Item{p, ws}},
            Equal.sym(
              Maybe<&2, Run.Files.Item>,
              Crits.Crit.get(Run.Files.Item, m, Run.Files.key(p)),
              Crits.Crit.lookup(Run.Files.Item, m, Run.Files.key(p)),
              Crits.Crit.get_lookup(~Run.Files.Item, m, Run.Files.key(p))(w)
            ),
            Files.get.of_some(Crits.Crit.get(Run.Files.Item, m, Run.Files.key(p)), p, ws)(h)
          )
        )(Files.holds_self(p, ws))
      )
