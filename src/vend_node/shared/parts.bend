import Base
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../run/parts.bend as Run

# Parts
# -----
# Content stored once by hash: a dict from the code of a hash to words. A read
# hashes what it finds and answers only when that is the hash asked, so an
# entry under a wrong key holds nothing, and each law holds for every value of
# the type, with no premise on SHA-256.

# the parts: words, each under the code of its hash
type Parts is Data:
  Parts{dict: Crits.Dict(List<&2, U32>)}

# the words of the hash h in d
def Parts.get(d: Parts, +h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  match d:
    case Parts{t}:
      Run.Parts.get.of(Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)), h)

# no part
def Parts.new() -> Parts:
  Parts{Crits.Dict.new(~List<&2, U32>)}

# d with the words ws under the hash h, unless d holds h
def Parts.put.if(held: Bool, d: Parts, h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  match held d:
    case True{} d:
      d
    case False{} Parts{t}:
      Parts{Crits.Dict.set(~List<&2, U32>, t, Run.Parts.key(h), ws)}

# d with the words ws under their hash h: what d holds under it stays
def Parts.put.at(d: Parts, +h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  +d = d
  Parts.put.if(Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)), d, h, ws)

# d with the words ws under their hash: what d holds under it stays
def Parts.put(d: Parts, +ws: List<&2, U32>) -> Parts:
  Parts.put.at(d, Hashes.Sha.hash(ws), ws)

# the seen keys s, with k unless it was seen
def Parts.uniq.seen(was: Bool, s: Crits.Dict(Unit), k: List<&2, U32>) -> Crits.Dict(Unit):
  match was:
    case True{}:
      s
    case False{}:
      Crits.Dict.set(~Unit, s, k, Unit{})

# the hashes hs, each once, but for those whose key is in seen
def Parts.uniq(hs: List<&2, Hashes.Hash>, +seen: Crits.Dict(Unit)) -> List<&2, Hashes.Hash>:
  match hs:
    case Nil{}:
      []
    case Con{+h, r}:
      Run.Parts.uniq.cons(
        Crits.Dict.has(Unit, seen, Run.Parts.key(h)),
        h,
        Parts.uniq(
          r,
          Parts.uniq.seen(Crits.Dict.has(Unit, seen, Run.Parts.key(h)), seen, Run.Parts.key(h))
        )
      )

# the hashes held in d, each once
def Parts.list(d: Parts) -> List<&2, Hashes.Hash>:
  match d:
    case Parts{t}:
      Parts.uniq(Run.Parts.list.go(Crits.Dict.entries(List<&2, U32>, t)), Crits.Dict.new(~Unit))

# a with the words ws under their hash h, when hit
def Parts.join.add(hit: Bool, a: Parts, h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  match hit:
    case True{}:
      Parts.put.at(a, h, ws)
    case False{}:
      a

# a with the words of each of the entries es whose key is the code of their hash
def Parts.join.go(es: List<&2, Crits.Bind<List<&2, U32>>>, a: Parts) -> Parts:
  match es:
    case Nil{}:
      a
    case Con{Crits.Bind{k, +ws}, r}:
      Parts.join.go(
        r,
        Parts.join.add(
          Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
          a,
          Hashes.Sha.hash(ws),
          ws
        )
      )

# a with each part of b: what a holds stays
def Parts.join(a: Parts, b: Parts) -> Parts:
  match b:
    case Parts{t}:
      Parts.join.go(Crits.Dict.entries(List<&2, U32>, t), a)

# acc with the words m, if any, under the hash h
def Parts.only.add(m: Maybe<&2, List<&2, U32>>, h: Hashes.Hash, acc: Parts) -> Parts:
  match m acc:
    case None{} acc:
      acc
    case Some{ws} Parts{t}:
      Parts{Crits.Dict.set(~List<&2, U32>, t, Run.Parts.key(h), ws)}

# the parts of d whose hash is in hs
def Parts.only.go(hs: List<&2, Hashes.Hash>, +d: Parts) -> Parts:
  match hs:
    case Nil{}:
      Parts.new()
    case Con{+h, r}:
      Parts.only.add(Parts.get(d, h), h, Parts.only.go(r, d))

# the parts of d whose hash is in hs
def Parts.only(d: Parts, hs: List<&2, Hashes.Hash>) -> Parts:
  Parts.only.go(hs, d)

# the hashes hs differ from each other
def Parts.Distinct(hs: List<&2, Hashes.Hash>) -> Type:
  match hs:
    case Nil{}:
      Unit
    case Con{h, r}:
      {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h) == False{}: Bool} & Parts.Distinct(r)

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
    case Crits.Crit.Fork{r, p, None{}, z, +o}:
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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# an entry read at the key k that passes, passes at the head
def Binds.any_head(
  ~V: Data,
  ~G: Data,
  ~f: G -> Crits.Bind<V> -> Bool,
  k2: List<&2, U32>,
  w: V,
  +k: List<&2, U32>,
  v: V,
  g: G,
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
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
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
    case Crits.Crit.Leaf{+k2, w}:
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
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Laws of parts
# -------------

# two checks that hold together are equal
def Parts.iff(
  x: Bool,
  y: Bool
) -> (
  {x == True{}: Bool} -> {y == True{}: Bool}
) -> ({y == True{}: Bool} -> {x == True{}: Bool}) -> {x == y: Bool}:
  match x y:
    case True{} True{}:
      f => g => {==}
    case True{} False{}:
      f => g => Equal.sym(Bool, False{}, True{}, f({==}))
    case False{} True{}:
      f => g => g({==})
    case False{} False{}:
      f => g => {==}

# the first of two facts
def Parts.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

# the second of two facts
def Parts.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# a choice that holds with a head that fails holds by its rest
def Any.rest_of(
  hit: Bool,
  -rest: Unit -> Bool
) -> {
  hit == False{}: Bool
} -> {List.any.if(rest, hit) == True{}: Bool} -> {rest(Unit{}) == True{}: Bool}:
  match hit:
    case False{}:
      e => s => s
    case True{}:
      e => s => Empty.absurd({rest(Unit{}) == True{}: Bool}, Shared.Bool.true_ne_false(e))

# hashes with the same key are the same
def Parts.key_inj(
  a: Hashes.Hash,
  b: Hashes.Hash
) -> {Crits.Key.is_eq(Run.Parts.key(a), Run.Parts.key(b)) == True{}: Bool} -> {a == b: Hashes.Hash}:
  e => Codes.Code.is_eq_sound(
    ~Hashes.Hash,
    ~Hashes.Hash.code,
    ~Hashes.Hash.code.read,
    ~(h => r => Hashes.Hash.code_read(h, r)),
    a,
    b
  )(e)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a hash that equals another is not unequal to it
def Parts.eq_self_false(
  x: Hashes.Hash,
  -h: Hashes.Hash,
  e: {x == h: Hashes.Hash}
) -> {Hashes.Hash.is_eq(x, h) == False{}: Bool} -> Empty:
  %e: {Hashes.Hash.is_eq(x, _) == False{}: Bool} -> Empty
  n => Shared.Bool.true_ne_false(
    Equal.trans(
      Bool,
      True{},
      Hashes.Hash.is_eq(x, x),
      False{},
      Equal.sym(Bool, Hashes.Hash.is_eq(x, x), True{}, Hashes.Hash.is_eq_refl(x)),
      n
    )
  )

# the keys of two unequal hashes are unequal, when their test is b
def Parts.key_ne.at(
  +x: Hashes.Hash,
  h: Hashes.Hash,
  b: Bool
) -> {
  Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)) == b: Bool
} -> {Hashes.Hash.is_eq(x, h) == False{}: Bool} -> {b == False{}: Bool}:
  match b:
    case False{}:
      e => n => {==}
    case True{}:
      e => n => Empty.absurd(
        {True{} == False{}: Bool},
        Parts.eq_self_false(x, h, Equal.sym(Hashes.Hash, h, x, Parts.key_inj(h, x)(e)))(n)
      )

# the keys of two unequal hashes are unequal
def Parts.key_ne(
  +x: Hashes.Hash,
  +h: Hashes.Hash
) -> {
  Hashes.Hash.is_eq(x, h) == False{}: Bool
} -> {Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)) == False{}: Bool}:
  n => Parts.key_ne.at(x, h, Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)))({==})(n)

# Parts.get.of_some when the test of the hashes is c
def Parts.get.of_some.at(
  ws2: List<&2, U32>,
  h: Hashes.Hash,
  -ws: List<&2, U32>,
  c: Bool
) -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), h) == c: Bool
} -> {
  Bool.pick(Maybe<&2, List<&2, U32>>, c, Some{ws2}, None{}) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {Some{ws2} == Some{ws}: Maybe<&2, List<&2, U32>>}
  & {Hashes.Sha.hash(ws) == h: Hashes.Hash}:
  match c:
    case True{}:
      e => s =>
        %Shared.Maybe.some_inj(
          List<&2, U32>,
          ws2,
          ws,
          s
        ): {Some{ws2} == Some{_}: Maybe<&2, List<&2, U32>>}
          & {Hashes.Sha.hash(_) == h: Hashes.Hash}
        ({==}, Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws2), h)(e))
    case False{}:
      e => s => Empty.absurd(
        {Some{ws2} == Some{ws}: Maybe<&2, List<&2, U32>>} & {Hashes.Sha.hash(ws) == h: Hashes.Hash},
        Shared.Maybe.none_ne_some(List<&2, U32>, ws, s)
      )

# words that answer ws under the hash h are ws, and h is their hash
def Parts.get.of_some(
  m: Maybe<&2, List<&2, U32>>,
  +h: Hashes.Hash,
  -ws: List<&2, U32>
) -> {
  Run.Parts.get.of(m, h) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {m == Some{ws}: Maybe<&2, List<&2, U32>>}
  & {Hashes.Sha.hash(ws) == h: Hashes.Hash}:
  match m:
    case None{}:
      s => Empty.absurd(
        {None{} == Some{ws}: Maybe<&2, List<&2, U32>>} & {Hashes.Sha.hash(ws) == h: Hashes.Hash},
        Shared.Maybe.none_ne_some(List<&2, U32>, ws, s)
      )
    case Some{+ws2}:
      s => Parts.get.of_some.at(ws2, h, ws, Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), h))({==})(s)

# the words held under a hash have that hash
def Parts.part_is(
  d: Parts,
  +h: Hashes.Hash,
  -ws: List<&2, U32>
) -> {
  Parts.get(d, h) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {Hashes.Sha.hash(ws) == h: Hashes.Hash}:
  match d:
    case Parts{t}:
      s => Parts.snd(
        {Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)) == Some{ws}: Maybe<&2, List<&2, U32>>},
        {Hashes.Sha.hash(ws) == h: Hashes.Hash},
        Parts.get.of_some(Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)), h, ws)(s)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# Parts.get_put when d holds h or not
def Parts.get_put.at(
  b: Bool,
  d: Parts,
  +h: Hashes.Hash,
  ws: List<&2, U32>
) -> {
  Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)) == b: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == True{}: Bool
} -> {Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts.put.if(b, d, h, ws), h)) == True{}: Bool}:
  match b d:
    case True{} d:
      e => ok => e
    case False{} Parts{t}:
      e => ok =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Crits.Dict.get(
            List<&2, U32>,
            Crits.Dict.set(~List<&2, U32>, t, Run.Parts.key(h), ws),
            Run.Parts.key(h)
          ),
          Bool.pick(
            Maybe<&2, List<&2, U32>>,
            Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(h)),
            Some{ws},
            Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h))
          ),
          Crits.Dict.get_set(~List<&2, U32>, t, Run.Parts.key(h), ws, Run.Parts.key(h))
        ): {Maybe.is_some(&2, List<&2, U32>, Run.Parts.get.of(_, h)) == True{}: Bool}
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(h)),
          True{},
          Crits.Key.is_eq_refl(Run.Parts.key(h))
        ): {
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Run.Parts.get.of(
              Bool.pick(
                Maybe<&2, List<&2, U32>>,
                _,
                Some{ws},
                Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h))
              ),
              h
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
          True{},
          ok
        ): {
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Bool.pick(Maybe<&2, List<&2, U32>>, _, Some{ws}, None{})
          )
            == True{}: Bool
        }
        {==}

# words that were put are held under their hash
def Parts.get_put(
  d: Parts,
  +ws: List<&2, U32>
) -> {
  Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts.put(d, ws), Hashes.Sha.hash(ws))) == True{}: Bool
}:
  +d = d
  Parts.get_put.at(
    Maybe.is_some(&2, List<&2, U32>, Parts.get(d, Hashes.Sha.hash(ws))),
    d,
    Hashes.Sha.hash(ws),
    ws
  )({==})(Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws)))

# the seen keys hold the key of h as that of an equal x
def Parts.has_at(
  x: Hashes.Hash,
  -h: Hashes.Hash,
  seen: Crits.Dict(Unit),
  -b: Bool
) -> {
  x == h: Hashes.Hash
} -> {
  Crits.Dict.has(Unit, seen, Run.Parts.key(x)) == b: Bool
} -> {Crits.Dict.has(Unit, seen, Run.Parts.key(h)) == b: Bool}:
  e => eb =>
    %e: {Crits.Dict.has(Unit, seen, Run.Parts.key(_)) == b: Bool}
    eb

# the seen keys with k hold k
def Parts.has_set_same(
  seen: Crits.Dict(Unit),
  +k: List<&2, U32>
) -> {Crits.Dict.has(Unit, Crits.Dict.set(~Unit, seen, k, Unit{}), k) == True{}: Bool}:
  %Equal.sym(
    Maybe<&2, Unit>,
    Crits.Dict.get(Unit, Crits.Dict.set(~Unit, seen, k, Unit{}), k),
    Bool.pick(Maybe<&2, Unit>, Crits.Key.is_eq(k, k), Some{Unit{}}, Crits.Dict.get(Unit, seen, k)),
    Crits.Dict.get_set(~Unit, seen, k, Unit{}, k)
  ): {Maybe.is_some(&2, Unit, _) == True{}: Bool}
  %Equal.sym(
    Bool,
    Crits.Key.is_eq(k, k),
    True{},
    Crits.Key.is_eq_refl(k)
  ): {
    Maybe.is_some(
      &2,
      Unit,
      Bool.pick(Maybe<&2, Unit>, _, Some{Unit{}}, Crits.Dict.get(Unit, seen, k))
    )
      == True{}: Bool
  }
  {==}

# the seen keys with k hold another key q as before
def Parts.has_set_other(
  seen: Crits.Dict(Unit),
  k: List<&2, U32>,
  q: List<&2, U32>
) -> {
  Crits.Key.is_eq(q, k) == False{}: Bool
} -> {
  Crits.Dict.has(
    Unit,
    Crits.Dict.set(~Unit, seen, k, Unit{}),
    q
  )
    == Crits.Dict.has(Unit, seen, q): Bool
}:
  n =>
    %Equal.sym(
      Maybe<&2, Unit>,
      Crits.Dict.get(Unit, Crits.Dict.set(~Unit, seen, k, Unit{}), q),
      Bool.pick(
        Maybe<&2, Unit>,
        Crits.Key.is_eq(q, k),
        Some{Unit{}},
        Crits.Dict.get(Unit, seen, q)
      ),
      Crits.Dict.get_set(~Unit, seen, k, Unit{}, q)
    ): {Maybe.is_some(&2, Unit, _) == Crits.Dict.has(Unit, seen, q): Bool}
    %Equal.sym(
      Bool,
      Crits.Key.is_eq(q, k),
      False{},
      n
    ): {
      Maybe.is_some(
        &2,
        Unit,
        Bool.pick(Maybe<&2, Unit>, _, Some{Unit{}}, Crits.Dict.get(Unit, seen, q))
      )
        == Crits.Dict.has(Unit, seen, q): Bool
    }
    {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a check that needs an unseen key fails when the key is seen
def Parts.seen_false(
  s: Bool,
  -rr: Bool
) -> {s == True{}: Bool} -> {Bool.and(Bool.not(s), rr) == False{}: Bool}:
  match s:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({rr == False{}: Bool}, Shared.Bool.false_ne_true(e))

# Parts.uniq_contains for a first hash x: b says it was seen, c that it is h
def Parts.uniq_contains.at(
  +x: Hashes.Hash,
  +h: Hashes.Hash,
  r: List<&2, Hashes.Hash>,
  +seen: Crits.Dict(Unit),
  b: Bool,
  c: Bool
) -> {
  Crits.Dict.has(Unit, seen, Run.Parts.key(x)) == b: Bool
} -> {
  Hashes.Hash.is_eq(x, h) == c: Bool
} -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Parts.uniq(r, Parts.uniq.seen(b, seen, Run.Parts.key(x))),
    h
  )
    == Bool.and(
      Bool.not(Crits.Dict.has(Unit, Parts.uniq.seen(b, seen, Run.Parts.key(x)), Run.Parts.key(h))),
      List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)
    ): Bool
} -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Run.Parts.uniq.cons(b, x, Parts.uniq(r, Parts.uniq.seen(b, seen, Run.Parts.key(x)))),
    h
  )
    == Bool.and(
      Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))),
      List.any.if(u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h), c)
    ): Bool
}:
  match b c:
    case True{} True{}:
      +eb => +ec => ih =>
        %Equal.sym(
          Bool,
          Crits.Dict.has(Unit, seen, Run.Parts.key(h)),
          True{},
          Parts.has_at(x, h, seen, True{})(Hashes.Hash.is_eq_sound(x, h)(ec))(eb)
        ): {
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Parts.uniq(r, seen),
            h
          )
            == Bool.and(Bool.not(_), True{}): Bool
        }
        Equal.trans(
          Bool,
          List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Parts.uniq(r, seen), h),
          Bool.and(
            Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))),
            List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)
          ),
          False{},
          ih,
          Parts.seen_false(
            Crits.Dict.has(Unit, seen, Run.Parts.key(h)),
            List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)
          )(Parts.has_at(x, h, seen, True{})(Hashes.Hash.is_eq_sound(x, h)(ec))(eb))
        )
    case True{} False{}:
      eb => ec => ih => ih
    case False{} True{}:
      +eb => +ec => ih =>
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(x, h),
          True{},
          ec
        ): {
          List.any.if(
            u => List.contains(
              ~Hashes.Hash,
              ~Hashes.Hash.is_eq,
              Parts.uniq(r, Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{})),
              h
            ),
            _
          )
            == Bool.and(Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))), True{}): Bool
        }
        %Equal.sym(
          Bool,
          Crits.Dict.has(Unit, seen, Run.Parts.key(h)),
          False{},
          Parts.has_at(x, h, seen, False{})(Hashes.Hash.is_eq_sound(x, h)(ec))(eb)
        ): {True{} == Bool.and(Bool.not(_), True{}): Bool}
        {==}
    case False{} False{}:
      +eb => +ec => ih =>
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(x, h),
          False{},
          ec
        ): {
          List.any.if(
            u => List.contains(
              ~Hashes.Hash,
              ~Hashes.Hash.is_eq,
              Parts.uniq(r, Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{})),
              h
            ),
            _
          )
            == Bool.and(
              Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))),
              List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)
            ): Bool
        }
        %Parts.has_set_other(
          seen,
          Run.Parts.key(x),
          Run.Parts.key(h)
        )(
          Parts.key_ne(x, h)(ec)
        ): {
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Parts.uniq(r, Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{})),
            h
          )
            == Bool.and(Bool.not(_), List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)): Bool
        }
        ih

# a hash is among the unique ones when it was not seen and is among them all
def Parts.uniq_contains(
  hs: List<&2, Hashes.Hash>,
  +seen: Crits.Dict(Unit),
  +h: Hashes.Hash
) -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Parts.uniq(hs, seen),
    h
  )
    == Bool.and(
      Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))),
      List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, hs, h)
    ): Bool
}:
  match hs:
    case Nil{}:
      Equal.sym(
        Bool,
        Bool.and(Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))), False{}),
        False{},
        Shared.Bool.and_false_right(Bool.not(Crits.Dict.has(Unit, seen, Run.Parts.key(h))))
      )
    case Con{+x, +r}:
      Parts.uniq_contains.at(
        x,
        h,
        r,
        seen,
        Crits.Dict.has(Unit, seen, Run.Parts.key(x)),
        Hashes.Hash.is_eq(x, h)
      )(
        {==}
      )(
        {==}
      )(
        Parts.uniq_contains(
          r,
          Parts.uniq.seen(Crits.Dict.has(Unit, seen, Run.Parts.key(x)), seen, Run.Parts.key(x)),
          h
        )
      )

# Parts.uniq_distinct for a first hash x that was seen or not
def Parts.uniq_distinct.at(
  +x: Hashes.Hash,
  r: List<&2, Hashes.Hash>,
  +seen: Crits.Dict(Unit),
  b: Bool
) -> {
  Crits.Dict.has(Unit, seen, Run.Parts.key(x)) == b: Bool
} -> Parts.Distinct(
  Parts.uniq(r, Parts.uniq.seen(b, seen, Run.Parts.key(x)))
) -> Parts.Distinct(
  Run.Parts.uniq.cons(b, x, Parts.uniq(r, Parts.uniq.seen(b, seen, Run.Parts.key(x))))
):
  match b:
    case True{}:
      eb => ih => ih
    case False{}:
      eb => ih => (
        Equal.trans(
          Bool,
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Parts.uniq(r, Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{})),
            x
          ),
          Bool.and(
            Bool.not(
              Crits.Dict.has(
                Unit,
                Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{}),
                Run.Parts.key(x)
              )
            ),
            List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, x)
          ),
          False{},
          Parts.uniq_contains(r, Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{}), x),
          Parts.seen_false(
            Crits.Dict.has(
              Unit,
              Crits.Dict.set(~Unit, seen, Run.Parts.key(x), Unit{}),
              Run.Parts.key(x)
            ),
            List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, x)
          )(Parts.has_set_same(seen, Run.Parts.key(x)))
        ),
        ih
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the unique hashes differ from each other
def Parts.uniq_distinct(
  hs: List<&2, Hashes.Hash>,
  +seen: Crits.Dict(Unit)
) -> Parts.Distinct(Parts.uniq(hs, seen)):
  match hs:
    case Nil{}:
      Unit{}
    case Con{+x, +r}:
      Parts.uniq_distinct.at(
        x,
        r,
        seen,
        Crits.Dict.has(Unit, seen, Run.Parts.key(x))
      )(
        {==}
      )(
        Parts.uniq_distinct(
          r,
          Parts.uniq.seen(Crits.Dict.has(Unit, seen, Run.Parts.key(x)), seen, Run.Parts.key(x))
        )
      )

# the entry b counts, and its hash is h
def Parts.holds(h: Hashes.Hash, b: Crits.Bind<List<&2, U32>>) -> Bool:
  match b:
    case Crits.Bind{k, +ws}:
      Bool.and(
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h)
      )

# an entry under the key of h whose hash x is h counts
def Parts.holds_self(
  -h: Hashes.Hash,
  +x: Hashes.Hash
) -> {
  x == h: Hashes.Hash
} -> {
  Bool.and(
    Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)),
    Hashes.Hash.is_eq(x, h)
  )
    == True{}: Bool
}:
  e =>
    %e: {
      Bool.and(
        Crits.Key.is_eq(Run.Parts.key(_), Run.Parts.key(x)),
        Hashes.Hash.is_eq(x, _)
      )
        == True{}: Bool
    }
    %Equal.sym(
      Bool,
      Crits.Key.is_eq(Run.Parts.key(x), Run.Parts.key(x)),
      True{},
      Crits.Key.is_eq_refl(Run.Parts.key(x))
    ): {Bool.and(_, Hashes.Hash.is_eq(x, x)) == True{}: Bool}
    %Equal.sym(
      Bool,
      Hashes.Hash.is_eq(x, x),
      True{},
      Hashes.Hash.is_eq_refl(x)
    ): {Bool.and(True{}, _) == True{}: Bool}
    {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# Parts.list_any for a first entry whose key test is a and hash test is c
def Parts.list_any.at(
  a: Bool,
  c: Bool,
  x: Hashes.Hash,
  h: Hashes.Hash,
  rest: List<&2, Hashes.Hash>,
  -anyr: Bool
) -> {
  Hashes.Hash.is_eq(x, h) == c: Bool
} -> (
  {
    anyr == True{}: Bool
  } -> {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h) == True{}: Bool}
) -> {
  List.any.if(u => anyr, Bool.and(a, c)) == True{}: Bool
} -> {
  List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Run.Parts.list.if(a, x, rest), h) == True{}: Bool
}:
  match a c:
    case True{} True{}:
      e => ih => s => Any.hit(
        Hashes.Hash.is_eq(x, h),
        u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h)
      )(e)
    case True{} False{}:
      e => ih => s => Any.rest(
        Hashes.Hash.is_eq(x, h),
        u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h)
      )(ih(s))
    case False{} True{}:
      e => ih => s => ih(s)
    case False{} False{}:
      e => ih => s => ih(s)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the hash of an entry that counts is among the hashes
def Parts.list_any(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +h: Hashes.Hash
) -> {
  Binds.any(~List<&2, U32>, ~Hashes.Hash, ~(g => b => Parts.holds(g, b)), es, h) == True{}: Bool
} -> {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Run.Parts.list.go(es), h) == True{}: Bool}:
  match es:
    case Nil{}:
      s => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(s))
    case Con{Crits.Bind{k, +ws}, +r}:
      s => Parts.list_any.at(
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
        Hashes.Sha.hash(ws),
        h,
        Run.Parts.list.go(r),
        Binds.any(~List<&2, U32>, ~Hashes.Hash, ~(g => b => Parts.holds(g, b)), r, h)
      )({==})(Parts.list_any(r, h))(s)

# Parts.held_in for the words ws read under the key of h, with their hash test c
def Parts.held_in.at(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash,
  +ws: List<&2, U32>,
  c: Bool
) -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == c: Bool
} -> {
  Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Bool.pick(Maybe<&2, List<&2, U32>>, c, Some{ws}, None{})
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
    h
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      ec => e => s => Parts.list_any(
        Crits.Crit.entries(List<&2, U32>, m),
        h
      )(
        Binds.any_hit(
          ~List<&2, U32>,
          ~Hashes.Hash,
          ~(g => b => Parts.holds(g, b)),
          m,
          [],
          h,
          Run.Parts.key(h),
          ws
        )(
          e
        )(
          Parts.holds_self(
            h,
            Hashes.Sha.hash(ws)
          )(Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws), h)(ec))
        )
      )
    case False{}:
      ec => e => s => Empty.absurd(
        {
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
            h
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(s)
      )

# Parts.held_in for what m holds under the key of h
def Parts.held_in.of(
  m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash,
  g: Maybe<&2, List<&2, U32>>
) -> {
  Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)) == g: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.is_some(&2, List<&2, U32>, Run.Parts.get.of(g, h)) == True{}: Bool
} -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
    h
  )
    == True{}: Bool
}:
  match g:
    case None{}:
      e => s => Empty.absurd(
        {
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
            h
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(s)
      )
    case Some{+ws}:
      e => s => Parts.held_in.at(m, h, ws, Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h))({==})(e)(s)

# a hash that m holds is among the hashes of its entries
def Parts.held_in(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash
) -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
    h
  )
    == True{}: Bool
}:
  s => Parts.held_in.of(m, h, Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)))({==})(s)

# what m holds under the key k of the hash x is what it holds under that of an equal h
def Parts.look_at(
  k: List<&2, U32>,
  x: Hashes.Hash,
  -h: Hashes.Hash,
  m: Crits.Crit<List<&2, U32>>,
  -ws: List<&2, U32>
) -> {
  k == Run.Parts.key(x): List<&2, U32>
} -> {
  x == h: Hashes.Hash
} -> {
  Crits.Crit.lookup(List<&2, U32>, m, k) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)) == Some{ws}: Maybe<&2, List<&2, U32>>}:
  e1 => e2 => lk =>
    %e2: {
      Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(_)) == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %e1: {Crits.Crit.lookup(List<&2, U32>, m, _) == Some{ws}: Maybe<&2, List<&2, U32>>}
    lk

# Parts.in_held for a first entry whose key test is a and hash test is c
def Parts.in_held.at(
  +k: List<&2, U32>,
  +ws: List<&2, U32>,
  m: Crits.Crit<List<&2, U32>>,
  h: Hashes.Hash,
  rest: List<&2, Hashes.Hash>,
  a: Bool,
  c: Bool
) -> {
  Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))) == a: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == c: Bool
} -> {
  Crits.Crit.lookup(List<&2, U32>, m, k) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> (
  {
    List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h) == True{}: Bool
  } -> {
    Maybe.is_some(
      &2,
      List<&2, U32>,
      Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
    )
      == True{}: Bool
  }
) -> {
  List.contains(
    ~Hashes.Hash,
    ~Hashes.Hash.is_eq,
    Run.Parts.list.if(a, Hashes.Sha.hash(ws), rest),
    h
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
  )
    == True{}: Bool
}:
  match a c:
    case True{} True{}:
      ea => +ec => lk => ih => s =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
          Some{ws},
          Parts.look_at(
            k,
            Hashes.Sha.hash(ws),
            h,
            m,
            ws
          )(
            Crits.Key.is_eq_sound(k, Run.Parts.key(Hashes.Sha.hash(ws)))(ea)
          )(Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws), h)(ec))(lk)
        ): {Maybe.is_some(&2, List<&2, U32>, Run.Parts.get.of(_, h)) == True{}: Bool}
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
          True{},
          ec
        ): {
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Bool.pick(Maybe<&2, List<&2, U32>>, _, Some{ws}, None{})
          )
            == True{}: Bool
        }
        {==}
    case True{} False{}:
      ea => ec => lk => ih => s => ih(
        Any.rest_of(
          Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
          u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h)
        )(ec)(s)
      )
    case False{} True{}:
      ea => ec => lk => ih => s => ih(s)
    case False{} False{}:
      ea => ec => lk => ih => s => ih(s)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a hash among those of the entries es, which are entries of m, is held in m
def Parts.in_held(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash
) -> Crits.Crit.agrees(
  List<&2, U32>,
  es,
  m
) -> {
  List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Run.Parts.list.go(es), h) == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
  )
    == True{}: Bool
}:
  match es:
    case Nil{}:
      ag => s => Empty.absurd(
        {
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(s)
      )
    case Con{Crits.Bind{+k, +ws}, +r}:
      +ag => s => Parts.in_held.at(
        k,
        ws,
        m,
        h,
        Run.Parts.list.go(r),
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h)
      )(
        {==}
      )(
        {==}
      )(
        Crits.Crit.agrees.hd(List<&2, U32>, k, ws, r, m, ag)
      )(s2 => Parts.in_held(r, m, h)(Crits.Crit.agrees.tl(List<&2, U32>, k, ws, r, m, ag))(s2))(s)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a well formed map holds a hash exactly when it is among the unique hashes of its entries
def Parts.held(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash
) -> {
  Crits.Crit.wf(~List<&2, U32>, m, 0n) == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Run.Parts.get.of(Crits.Crit.get(List<&2, U32>, m, Run.Parts.key(h)), h)
  )
    == List.contains(
      ~Hashes.Hash,
      ~Hashes.Hash.is_eq,
      Parts.uniq(Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)), Crits.Dict.new(~Unit)),
      h
    ): Bool
}:
  +w =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Crits.Crit.get(List<&2, U32>, m, Run.Parts.key(h)),
      Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
      Crits.Crit.get_lookup(~List<&2, U32>, m, Run.Parts.key(h))(w)
    ): {
      Maybe.is_some(
        &2,
        List<&2, U32>,
        Run.Parts.get.of(_, h)
      )
        == List.contains(
          ~Hashes.Hash,
          ~Hashes.Hash.is_eq,
          Parts.uniq(
            Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
            Crits.Dict.new(~Unit)
          ),
          h
        ): Bool
    }
    Equal.trans(
      Bool,
      Maybe.is_some(
        &2,
        List<&2, U32>,
        Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
      ),
      List.contains(
        ~Hashes.Hash,
        ~Hashes.Hash.is_eq,
        Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
        h
      ),
      List.contains(
        ~Hashes.Hash,
        ~Hashes.Hash.is_eq,
        Parts.uniq(Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)), Crits.Dict.new(~Unit)),
        h
      ),
      Parts.iff(
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
        ),
        List.contains(
          ~Hashes.Hash,
          ~Hashes.Hash.is_eq,
          Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
          h
        )
      )(
        s => Parts.held_in(m, h)(s)
      )(
        s => Parts.in_held(
          Crits.Crit.entries(List<&2, U32>, m),
          m,
          h
        )(
          Crits.Crit.sub_to_list(
            List<&2, U32>,
            m,
            [],
            m
          )(Crits.Crit.sub_self(~List<&2, U32>, m, 0n)(w))(Unit{})
        )(s)
      ),
      Equal.sym(
        Bool,
        List.contains(
          ~Hashes.Hash,
          ~Hashes.Hash.is_eq,
          Parts.uniq(
            Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
            Crits.Dict.new(~Unit)
          ),
          h
        ),
        List.contains(
          ~Hashes.Hash,
          ~Hashes.Hash.is_eq,
          Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
          h
        ),
        Parts.uniq_contains(
          Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
          Crits.Dict.new(~Unit),
          h
        )
      )
    )

# the hashes held differ from each other, and they are the hashes that d holds
def Parts.once(
  d: Parts
) -> Parts.Distinct(
  Parts.list(d)
)
  & (
    @h: Hashes.Hash -> {
      Maybe.is_some(
        &2,
        List<&2, U32>,
        Parts.get(d, h)
      )
        == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Parts.list(d), h): Bool
    }
  ):
  match d:
    case Parts{Tuple{+m, w}}:
      (
        Parts.uniq_distinct(
          Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
          Crits.Dict.new(~Unit)
        ),
        +h => Parts.held(m, h)(w)
      )

# More laws: put, join and only
# -----------------------------

# what d holds under a hash x, it holds under an equal h
def Parts.get_at(
  d: Parts,
  x: Hashes.Hash,
  -h: Hashes.Hash,
  -g: Maybe<&2, List<&2, U32>>
) -> {
  x == h: Hashes.Hash
} -> {
  Parts.get(d, x) == g: Maybe<&2, List<&2, U32>>
} -> {Parts.get(d, h) == g: Maybe<&2, List<&2, U32>>}:
  e => eg =>
    %e: {Parts.get(d, _) == g: Maybe<&2, List<&2, U32>>}
    eg

# d holds a hash x as it holds an equal h
def Parts.get_at.some(
  d: Parts,
  x: Hashes.Hash,
  -h: Hashes.Hash,
  -b: Bool
) -> {
  x == h: Hashes.Hash
} -> {
  Maybe.is_some(&2, List<&2, U32>, Parts.get(d, x)) == b: Bool
} -> {Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)) == b: Bool}:
  e => eb =>
    %e: {Maybe.is_some(&2, List<&2, U32>, Parts.get(d, _)) == b: Bool}
    eb

# equal hashes have the same key
def Parts.key_same(
  x: Hashes.Hash,
  -h: Hashes.Hash
) -> {x == h: Hashes.Hash} -> {Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)) == True{}: Bool}:
  e =>
    %e: {Crits.Key.is_eq(Run.Parts.key(_), Run.Parts.key(x)) == True{}: Bool}
    Crits.Key.is_eq_refl(Run.Parts.key(x))

# equal hashes pass the test of hashes
def Parts.heq_of(
  a: Hashes.Hash,
  -b: Hashes.Hash
) -> {a == b: Hashes.Hash} -> {Hashes.Hash.is_eq(a, b) == True{}: Bool}:
  e =>
    %e: {Hashes.Hash.is_eq(a, _) == True{}: Bool}
    Hashes.Hash.is_eq_refl(a)

# words whose hash is x have the hash of an equal h
def Parts.ok_at(
  x: Hashes.Hash,
  -h: Hashes.Hash,
  -y: Hashes.Hash
) -> {
  x == h: Hashes.Hash
} -> {Hashes.Hash.is_eq(y, x) == True{}: Bool} -> {Hashes.Hash.is_eq(y, h) == True{}: Bool}:
  e => ok =>
    %e: {Hashes.Hash.is_eq(y, _) == True{}: Bool}
    ok

# a write under the key asked, of words with the hash asked, is read back
def Parts.set_hit(
  kq: Bool,
  -raw: Maybe<&2, List<&2, U32>>,
  ws: List<&2, U32>,
  h: Hashes.Hash
) -> {
  kq == True{}: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == True{}: Bool
} -> {
  Run.Parts.get.of(
    Bool.pick(Maybe<&2, List<&2, U32>>, kq, Some{ws}, raw),
    h
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  e1 => ok =>
    %Equal.sym(
      Bool,
      kq,
      True{},
      e1
    ): {
      Run.Parts.get.of(
        Bool.pick(Maybe<&2, List<&2, U32>>, _, Some{ws}, raw),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
      True{},
      ok
    ): {
      Bool.pick(Maybe<&2, List<&2, U32>>, _, Some{ws}, None{}) == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    {==}

# what a dict with a write holds under k, read as a part
def Parts.get_set_of(
  t: Crits.Dict(List<&2, U32>),
  k0: List<&2, U32>,
  ws: List<&2, U32>,
  k: List<&2, U32>,
  h: Hashes.Hash
) -> {
  Run.Parts.get.of(
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Crits.Key.is_eq(k, k0),
      Some{ws},
      Crits.Dict.get(List<&2, U32>, t, k)
    ),
    h
  )
    == Run.Parts.get.of(
      Crits.Dict.get(List<&2, U32>, Crits.Dict.set(~List<&2, U32>, t, k0, ws), k),
      h
    ): Maybe<&2, List<&2, U32>>
}:
  %Crits.Dict.get_set(
    ~List<&2, U32>,
    t,
    k0,
    ws,
    k
  ): {
    Run.Parts.get.of(
      _,
      h
    )
      == Run.Parts.get.of(
        Crits.Dict.get(List<&2, U32>, Crits.Dict.set(~List<&2, U32>, t, k0, ws), k),
        h
      ): Maybe<&2, List<&2, U32>>
  }
  {==}

# a put that d already holds changes nothing: the choice of the law is x
def Parts.put_same(
  c: Bool,
  s: Bool,
  x: Maybe<&2, List<&2, U32>>,
  -ws: List<&2, U32>
) -> {
  c == True{}: Bool
} -> {
  s == True{}: Bool
} -> {
  x
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(c, Bool.not(s)),
      Some{ws},
      x
    ): Maybe<&2, List<&2, U32>>
}:
  e1 => e2 =>
    %Equal.sym(
      Bool,
      c,
      True{},
      e1
    ): {
      x
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(_, Bool.not(s)),
          Some{ws},
          x
        ): Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      s,
      True{},
      e2
    ): {
      x
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(True{}, Bool.not(_)),
          Some{ws},
          x
        ): Maybe<&2, List<&2, U32>>
    }
    {==}

# a put of another hash changes nothing: the choice of the law is x
def Parts.put_skip(
  c: Bool,
  -s: Bool,
  x: Maybe<&2, List<&2, U32>>,
  -ws: List<&2, U32>
) -> {
  c == False{}: Bool
} -> {
  x
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(c, Bool.not(s)),
      Some{ws},
      x
    ): Maybe<&2, List<&2, U32>>
}:
  e1 =>
    %Equal.sym(
      Bool,
      c,
      False{},
      e1
    ): {
      x
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(_, Bool.not(s)),
          Some{ws},
          x
        ): Maybe<&2, List<&2, U32>>
    }
    {==}

# a write of the hash asked, that was not held, is read back
def Parts.put_hit(
  kq: Bool,
  c: Bool,
  s: Bool,
  -raw: Maybe<&2, List<&2, U32>>,
  -old: Maybe<&2, List<&2, U32>>,
  ws: List<&2, U32>,
  h: Hashes.Hash
) -> {
  kq == True{}: Bool
} -> {
  c == True{}: Bool
} -> {
  s == False{}: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == True{}: Bool
} -> {
  Run.Parts.get.of(
    Bool.pick(Maybe<&2, List<&2, U32>>, kq, Some{ws}, raw),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(c, Bool.not(s)),
      Some{ws},
      old
    ): Maybe<&2, List<&2, U32>>
}:
  e1 => e2 => e3 => ok =>
    %Equal.sym(
      Bool,
      c,
      True{},
      e2
    ): {
      Run.Parts.get.of(
        Bool.pick(Maybe<&2, List<&2, U32>>, kq, Some{ws}, raw),
        h
      )
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(_, Bool.not(s)),
          Some{ws},
          old
        ): Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      s,
      False{},
      e3
    ): {
      Run.Parts.get.of(
        Bool.pick(Maybe<&2, List<&2, U32>>, kq, Some{ws}, raw),
        h
      )
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(True{}, Bool.not(_)),
          Some{ws},
          old
        ): Maybe<&2, List<&2, U32>>
    }
    Parts.set_hit(kq, raw, ws, h)(e1)(ok)

# a write of another hash is not read
def Parts.put_miss(
  kq: Bool,
  c: Bool,
  -s: Bool,
  -raw: Maybe<&2, List<&2, U32>>,
  ws: List<&2, U32>,
  h: Hashes.Hash
) -> {
  kq == False{}: Bool
} -> {
  c == False{}: Bool
} -> {
  Run.Parts.get.of(
    Bool.pick(Maybe<&2, List<&2, U32>>, kq, Some{ws}, raw),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(c, Bool.not(s)),
      Some{ws},
      Run.Parts.get.of(raw, h)
    ): Maybe<&2, List<&2, U32>>
}:
  e1 => e2 =>
    %Equal.sym(
      Bool,
      kq,
      False{},
      e1
    ): {
      Run.Parts.get.of(
        Bool.pick(Maybe<&2, List<&2, U32>>, _, Some{ws}, raw),
        h
      )
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(c, Bool.not(s)),
          Some{ws},
          Run.Parts.get.of(raw, h)
        ): Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      c,
      False{},
      e2
    ): {
      Run.Parts.get.of(
        raw,
        h
      )
        == Bool.pick(
          Maybe<&2, List<&2, U32>>,
          Bool.and(_, Bool.not(s)),
          Some{ws},
          Run.Parts.get.of(raw, h)
        ): Maybe<&2, List<&2, U32>>
    }
    {==}

# Parts.get_put_at when d holds h0 or not (b), and h0 is h or not (c)
def Parts.get_put_at.at(
  b: Bool,
  c: Bool,
  +d: Parts,
  +h0: Hashes.Hash,
  +ws: List<&2, U32>,
  +h: Hashes.Hash
) -> {
  Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h0)) == b: Bool
} -> {
  Hashes.Hash.is_eq(h0, h) == c: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h0) == True{}: Bool
} -> {
  Parts.get(
    Parts.put.if(b, d, h0, ws),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(
        Hashes.Hash.is_eq(h0, h),
        Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)))
      ),
      Some{ws},
      Parts.get(d, h)
    ): Maybe<&2, List<&2, U32>>
}:
  match b c d:
    case True{} True{} d:
      eb => +ec => ok => Parts.put_same(
        Hashes.Hash.is_eq(h0, h),
        Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)),
        Parts.get(d, h),
        ws
      )(ec)(Parts.get_at.some(d, h0, h, True{})(Hashes.Hash.is_eq_sound(h0, h)(ec))(eb))
    case True{} False{} d:
      eb => ec => ok => Parts.put_skip(
        Hashes.Hash.is_eq(h0, h),
        Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)),
        Parts.get(d, h),
        ws
      )(ec)
    case False{} True{} Parts{+t}:
      eb => +ec => ok =>
        %Parts.get_set_of(
          t,
          Run.Parts.key(h0),
          ws,
          Run.Parts.key(h),
          h
        ): {
          _
            == Bool.pick(
              Maybe<&2, List<&2, U32>>,
              Bool.and(
                Hashes.Hash.is_eq(h0, h),
                Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts{t}, h)))
              ),
              Some{ws},
              Parts.get(Parts{t}, h)
            ): Maybe<&2, List<&2, U32>>
        }
        Parts.put_hit(
          Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(h0)),
          Hashes.Hash.is_eq(h0, h),
          Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts{t}, h)),
          Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)),
          Parts.get(Parts{t}, h),
          ws,
          h
        )(
          Parts.key_same(h0, h)(Hashes.Hash.is_eq_sound(h0, h)(ec))
        )(
          ec
        )(
          Parts.get_at.some(Parts{t}, h0, h, False{})(Hashes.Hash.is_eq_sound(h0, h)(ec))(eb)
        )(Parts.ok_at(h0, h, Hashes.Sha.hash(ws))(Hashes.Hash.is_eq_sound(h0, h)(ec))(ok))
    case False{} False{} Parts{t}:
      eb => +ec => ok =>
        %Parts.get_set_of(
          t,
          Run.Parts.key(h0),
          ws,
          Run.Parts.key(h),
          h
        ): {
          _
            == Bool.pick(
              Maybe<&2, List<&2, U32>>,
              Bool.and(
                Hashes.Hash.is_eq(h0, h),
                Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts{t}, h)))
              ),
              Some{ws},
              Parts.get(Parts{t}, h)
            ): Maybe<&2, List<&2, U32>>
        }
        Parts.put_miss(
          Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(h0)),
          Hashes.Hash.is_eq(h0, h),
          Maybe.is_some(&2, List<&2, U32>, Parts.get(Parts{t}, h)),
          Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)),
          ws,
          h
        )(Parts.key_ne(h0, h)(ec))(ec)

# what a put under h0 holds under h: the new words when h0 is h and was not held, else what was held
def Parts.get_put_at(
  d: Parts,
  +h0: Hashes.Hash,
  ws: List<&2, U32>,
  +h: Hashes.Hash
) -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h0) == True{}: Bool
} -> {
  Parts.get(
    Parts.put.at(d, h0, ws),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(
        Hashes.Hash.is_eq(h0, h),
        Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)))
      ),
      Some{ws},
      Parts.get(d, h)
    ): Maybe<&2, List<&2, U32>>
}:
  +d = d
  ok => Parts.get_put_at.at(
    Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h0)),
    Hashes.Hash.is_eq(h0, h),
    d,
    h0,
    ws,
    h
  )({==})({==})(ok)

# what a put holds under h: the new words when their hash is h and was not held, else what was held
def Parts.get_put_all(
  d: Parts,
  +ws: List<&2, U32>,
  h: Hashes.Hash
) -> {
  Parts.get(
    Parts.put(d, ws),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
        Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)))
      ),
      Some{ws},
      Parts.get(d, h)
    ): Maybe<&2, List<&2, U32>>
}:
  Parts.get_put_at(d, Hashes.Sha.hash(ws), ws, h)(Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws)))

# the words ws when hit, else rest
def Parts.find.if(
  hit: Bool,
  ws: List<&2, U32>,
  rest: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, U32>>:
  match hit:
    case True{}:
      Some{ws}
    case False{}:
      rest

# the words of the first of the entries es that counts for the hash h: a clear def, for the laws
def Parts.find(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +h: Hashes.Hash
) -> Maybe<&2, List<&2, U32>>:
  match es:
    case Nil{}:
      None{}
    case Con{Crits.Bind{k, +ws}, r}:
      Parts.find.if(
        Bool.and(
          Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
          Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h)
        ),
        ws,
        Parts.find(r, h)
      )

# a put, then what follows, is what was held, else the put, else what follows
def Parts.or_put(
  c: Bool,
  x: Maybe<&2, List<&2, U32>>,
  -f: Maybe<&2, List<&2, U32>>,
  -ws: List<&2, U32>
) -> {
  Maybe.or(
    &2,
    List<&2, U32>,
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      Bool.and(c, Bool.not(Maybe.is_some(&2, List<&2, U32>, x))),
      Some{ws},
      x
    ),
    f
  )
    == Maybe.or(&2, List<&2, U32>, x, Parts.find.if(c, ws, f)): Maybe<&2, List<&2, U32>>
}:
  match c x:
    case True{} Some{y}:
      {==}
    case True{} None{}:
      {==}
    case False{} x:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# Parts.get_join_go for a first entry of the words ws: v says that it counts, hh is its hash
def Parts.get_join_go.at(
  v: Bool,
  +a: Parts,
  +hh: Hashes.Hash,
  ws: List<&2, U32>,
  +h: Hashes.Hash,
  -j: Maybe<&2, List<&2, U32>>,
  -f: Maybe<&2, List<&2, U32>>
) -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws), hh) == True{}: Bool
} -> {
  j
    == Maybe.or(
      &2,
      List<&2, U32>,
      Parts.get(Parts.join.add(v, a, hh, ws), h),
      f
    ): Maybe<&2, List<&2, U32>>
} -> {
  j
    == Maybe.or(
      &2,
      List<&2, U32>,
      Parts.get(a, h),
      Parts.find.if(Bool.and(v, Hashes.Hash.is_eq(hh, h)), ws, f)
    ): Maybe<&2, List<&2, U32>>
}:
  match v:
    case False{}:
      ok => ih => ih
    case True{}:
      ok => ih => Equal.trans(
        Maybe<&2, List<&2, U32>>,
        j,
        Maybe.or(&2, List<&2, U32>, Parts.get(Parts.put.at(a, hh, ws), h), f),
        Maybe.or(
          &2,
          List<&2, U32>,
          Parts.get(a, h),
          Parts.find.if(Hashes.Hash.is_eq(hh, h), ws, f)
        ),
        ih,
        (
          %Equal.sym(Maybe<&2, List<&2, U32>>, Parts.get(Parts.put.at(a, hh, ws), h), Bool.pick(Maybe<&2, List<&2, U32>>, Bool.and(Hashes.Hash.is_eq(hh, h), Bool.not(Maybe.is_some(&2, List<&2, U32>, Parts.get(a, h)))), Some{ws}, Parts.get(a, h)), Parts.get_put_at(a, hh, ws, h)(ok)): {Maybe.or(&2, List<&2, U32>, _, f) == Maybe.or(&2, List<&2, U32>, Parts.get(a, h), Parts.find.if(Hashes.Hash.is_eq(hh, h), ws, f)): Maybe<&2, List<&2, U32>>}
          Parts.or_put(Hashes.Hash.is_eq(hh, h), Parts.get(a, h), f, ws))
      )

# a with the entries es holds what a holds, else the first of es that counts
def Parts.get_join_go(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +a: Parts,
  +h: Hashes.Hash
) -> {
  Parts.get(
    Parts.join.go(es, a),
    h
  )
    == Maybe.or(&2, List<&2, U32>, Parts.get(a, h), Parts.find(es, h)): Maybe<&2, List<&2, U32>>
}:
  match es:
    case Nil{}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Maybe.or(&2, List<&2, U32>, Parts.get(a, h), None{}),
        Parts.get(a, h),
        Shared.Maybe.or_none(List<&2, U32>, Parts.get(a, h))
      )
    case Con{Crits.Bind{+k, +ws}, r}:
      Parts.get_join_go.at(
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
        a,
        Hashes.Sha.hash(ws),
        ws,
        h,
        Parts.get(
          Parts.join.go(
            r,
            Parts.join.add(
              Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
              a,
              Hashes.Sha.hash(ws),
              ws
            )
          ),
          h
        ),
        Parts.find(r, h)
      )(
        Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws))
      )(
        Parts.get_join_go(
          r,
          Parts.join.add(
            Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
            a,
            Hashes.Sha.hash(ws),
            ws
          ),
          h
        )
      )

# Parts.find_some for a first entry whose key test is a and hash test is c
def Parts.find_some.at(
  +k: List<&2, U32>,
  +ws2: List<&2, U32>,
  m: Crits.Crit<List<&2, U32>>,
  h: Hashes.Hash,
  -ws: List<&2, U32>,
  -f: Maybe<&2, List<&2, U32>>,
  a: Bool,
  c: Bool
) -> {
  Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws2))) == a: Bool
} -> {
  Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), h) == c: Bool
} -> {
  Crits.Crit.lookup(List<&2, U32>, m, k) == Some{ws2}: Maybe<&2, List<&2, U32>>
} -> (
  {
    f == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {
    Run.Parts.get.of(
      Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
      h
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
) -> {
  Parts.find.if(Bool.and(a, c), ws2, f) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {
  Run.Parts.get.of(
    Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
    h
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  match a c:
    case True{} True{}:
      ea => +ec => lk => ih => s =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
          Some{ws2},
          Parts.look_at(
            k,
            Hashes.Sha.hash(ws2),
            h,
            m,
            ws2
          )(
            Crits.Key.is_eq_sound(k, Run.Parts.key(Hashes.Sha.hash(ws2)))(ea)
          )(Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws2), h)(ec))(lk)
        ): {Run.Parts.get.of(_, h) == Some{ws}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), h),
          True{},
          ec
        ): {
          Bool.pick(
            Maybe<&2, List<&2, U32>>,
            _,
            Some{ws2},
            None{}
          )
            == Some{ws}: Maybe<&2, List<&2, U32>>
        }
        s
    case True{} False{}:
      ea => ec => lk => ih => s => ih(s)
    case False{} True{}:
      ea => ec => lk => ih => s => ih(s)
    case False{} False{}:
      ea => ec => lk => ih => s => ih(s)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the first of the entries es that counts for h, entries of m, is what m holds under h
def Parts.find_some(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash,
  -ws: List<&2, U32>
) -> Crits.Crit.agrees(
  List<&2, U32>,
  es,
  m
) -> {
  Parts.find(es, h) == Some{ws}: Maybe<&2, List<&2, U32>>
} -> {
  Run.Parts.get.of(
    Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
    h
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  match es:
    case Nil{}:
      ag => s => Empty.absurd(
        {
          Run.Parts.get.of(
            Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
            h
          )
            == Some{ws}: Maybe<&2, List<&2, U32>>
        },
        Shared.Maybe.none_ne_some(List<&2, U32>, ws, s)
      )
    case Con{Crits.Bind{+k, +ws2}, r}:
      +ag => s => Parts.find_some.at(
        k,
        ws2,
        m,
        h,
        ws,
        Parts.find(r, h),
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws2))),
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), h)
      )(
        {==}
      )(
        {==}
      )(
        Crits.Crit.agrees.hd(List<&2, U32>, k, ws2, r, m, ag)
      )(
        s2 => Parts.find_some(
          r,
          m,
          h,
          ws
        )(Crits.Crit.agrees.tl(List<&2, U32>, k, ws2, r, m, ag))(s2)
      )(s)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Parts.find_is for a first entry whose key test is a and hash test is c
def Parts.find_is.at(
  a: Bool,
  c: Bool,
  x: Hashes.Hash,
  h: Hashes.Hash,
  -ws: List<&2, U32>,
  -f: Maybe<&2, List<&2, U32>>,
  rest: List<&2, Hashes.Hash>
) -> {
  Hashes.Hash.is_eq(x, h) == c: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    f
  )
    == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h): Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Parts.find.if(Bool.and(a, c), ws, f)
  )
    == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Run.Parts.list.if(a, x, rest), h): Bool
}:
  match a c:
    case True{} True{}:
      ec => ih =>
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(x, h),
          True{},
          ec
        ): {
          True{}
            == List.any.if(u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h), _): Bool
        }
        {==}
    case True{} False{}:
      ec => ih =>
        %Equal.sym(
          Bool,
          Hashes.Hash.is_eq(x, h),
          False{},
          ec
        ): {
          Maybe.is_some(
            &2,
            List<&2, U32>,
            f
          )
            == List.any.if(u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, h), _): Bool
        }
        ih
    case False{} True{}:
      ec => ih => ih
    case False{} False{}:
      ec => ih => ih

# some entry of es counts for h exactly when h is among the hashes of es
def Parts.find_is(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +h: Hashes.Hash
) -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Parts.find(es, h)
  )
    == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Run.Parts.list.go(es), h): Bool
}:
  match es:
    case Nil{}:
      {==}
    case Con{Crits.Bind{k, +ws}, +r}:
      Parts.find_is.at(
        Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
        Hashes.Sha.hash(ws),
        h,
        ws,
        Parts.find(r, h),
        Run.Parts.list.go(r)
      )({==})(Parts.find_is(r, h))

# each entry of a well formed map is an entry of it, as a list
def Parts.agrees_self(
  +m: Crits.Crit<List<&2, U32>>
) -> {
  Crits.Crit.wf(~List<&2, U32>, m, 0n) == True{}: Bool
} -> Crits.Crit.agrees(List<&2, U32>, Crits.Crit.entries(List<&2, U32>, m), m):
  w => Crits.Crit.sub_to_list(
    List<&2, U32>,
    m,
    [],
    m
  )(Crits.Crit.sub_self(~List<&2, U32>, m, 0n)(w))(Unit{})

# a well formed map holds a hash exactly when it is among the hashes of its entries
def Parts.held_iff(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash
) -> {
  Crits.Crit.wf(~List<&2, U32>, m, 0n) == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, U32>,
    Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
  )
    == List.contains(
      ~Hashes.Hash,
      ~Hashes.Hash.is_eq,
      Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
      h
    ): Bool
}:
  w => Parts.iff(
    Maybe.is_some(
      &2,
      List<&2, U32>,
      Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
    ),
    List.contains(
      ~Hashes.Hash,
      ~Hashes.Hash.is_eq,
      Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
      h
    )
  )(
    s => Parts.held_in(m, h)(s)
  )(s => Parts.in_held(Crits.Crit.entries(List<&2, U32>, m), m, h)(Parts.agrees_self(m)(w))(s))

# nothing is what is not some
def Parts.none_of(
  x: Maybe<&2, List<&2, U32>>
) -> {
  Maybe.is_some(&2, List<&2, U32>, x) == False{}: Bool
} -> {None{} == x: Maybe<&2, List<&2, U32>>}:
  match x:
    case None{}:
      e => {==}
    case Some{y}:
      e => Empty.absurd({None{} == Some{y}: Maybe<&2, List<&2, U32>>}, Shared.Bool.true_ne_false(e))

# Parts.find_get for the first entry fv that counts
def Parts.find_get.of(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash,
  fv: Maybe<&2, List<&2, U32>>
) -> {
  Crits.Crit.wf(~List<&2, U32>, m, 0n) == True{}: Bool
} -> {
  Parts.find(Crits.Crit.entries(List<&2, U32>, m), h) == fv: Maybe<&2, List<&2, U32>>
} -> {
  fv
    == Run.Parts.get.of(
      Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
      h
    ): Maybe<&2, List<&2, U32>>
}:
  match fv:
    case Some{ws}:
      w => e => Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h),
        Some{ws},
        Parts.find_some(Crits.Crit.entries(List<&2, U32>, m), m, h, ws)(Parts.agrees_self(m)(w))(e)
      )
    case None{}:
      w => e => Parts.none_of(
        Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
      )(
        Equal.trans(
          Bool,
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Run.Parts.get.of(Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)), h)
          ),
          List.contains(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
            h
          ),
          False{},
          Parts.held_iff(m, h)(w),
          Equal.trans(
            Bool,
            List.contains(
              ~Hashes.Hash,
              ~Hashes.Hash.is_eq,
              Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
              h
            ),
            Maybe.is_some(&2, List<&2, U32>, Parts.find(Crits.Crit.entries(List<&2, U32>, m), h)),
            False{},
            Equal.sym(
              Bool,
              Maybe.is_some(&2, List<&2, U32>, Parts.find(Crits.Crit.entries(List<&2, U32>, m), h)),
              List.contains(
                ~Hashes.Hash,
                ~Hashes.Hash.is_eq,
                Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
                h
              ),
              Parts.find_is(Crits.Crit.entries(List<&2, U32>, m), h)
            ),
            Equal.cong(
              Maybe<&2, List<&2, U32>>,
              Bool,
              y => Maybe.is_some(&2, List<&2, U32>, y),
              Parts.find(Crits.Crit.entries(List<&2, U32>, m), h),
              None{},
              e
            )
          )
        )
      )

# the first entry of a well formed map that counts for h is what the map holds under h
def Parts.find_get(
  +m: Crits.Crit<List<&2, U32>>,
  +h: Hashes.Hash
) -> {
  Crits.Crit.wf(~List<&2, U32>, m, 0n) == True{}: Bool
} -> {
  Parts.find(
    Crits.Crit.entries(List<&2, U32>, m),
    h
  )
    == Run.Parts.get.of(
      Crits.Crit.get(List<&2, U32>, m, Run.Parts.key(h)),
      h
    ): Maybe<&2, List<&2, U32>>
}:
  +w =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Crits.Crit.get(List<&2, U32>, m, Run.Parts.key(h)),
      Crits.Crit.lookup(List<&2, U32>, m, Run.Parts.key(h)),
      Crits.Crit.get_lookup(~List<&2, U32>, m, Run.Parts.key(h))(w)
    ): {
      Parts.find(
        Crits.Crit.entries(List<&2, U32>, m),
        h
      )
        == Run.Parts.get.of(_, h): Maybe<&2, List<&2, U32>>
    }
    Parts.find_get.of(m, h, Parts.find(Crits.Crit.entries(List<&2, U32>, m), h))(w)({==})

# a join holds what a holds, else what b holds
def Parts.get_join(
  a: Parts,
  b: Parts,
  +h: Hashes.Hash
) -> {
  Parts.get(
    Parts.join(a, b),
    h
  )
    == Maybe.or(&2, List<&2, U32>, Parts.get(a, h), Parts.get(b, h)): Maybe<&2, List<&2, U32>>
}:
  match b:
    case Parts{Tuple{+m, w}}:
      %Parts.find_get(
        m,
        h
      )(
        w
      ): {
        Parts.get(
          Parts.join.go(Crits.Crit.entries(List<&2, U32>, m), a),
          h
        )
          == Maybe.or(&2, List<&2, U32>, Parts.get(a, h), _): Maybe<&2, List<&2, U32>>
      }
      Parts.get_join_go(Crits.Crit.entries(List<&2, U32>, m), a, h)

# a choice of nothing or nothing is that nothing
def Parts.pick_none(
  rc: Bool,
  y: Maybe<&2, List<&2, U32>>
) -> {
  y == None{}: Maybe<&2, List<&2, U32>>
} -> {Bool.pick(Maybe<&2, List<&2, U32>>, rc, y, None{}) == y: Maybe<&2, List<&2, U32>>}:
  match rc:
    case True{}:
      e => {==}
    case False{}:
      e => Equal.sym(Maybe<&2, List<&2, U32>>, y, None{}, e)

# Parts.get_only_go for a first hash x: g is what d holds under it, c says that it is h
def Parts.get_only_go.at(
  g: Maybe<&2, List<&2, U32>>,
  c: Bool,
  acc: Parts,
  +x: Hashes.Hash,
  +h: Hashes.Hash,
  +d: Parts,
  rc: Bool
) -> {
  Parts.get(d, x) == g: Maybe<&2, List<&2, U32>>
} -> {
  Hashes.Hash.is_eq(x, h) == c: Bool
} -> {
  Parts.get(
    acc,
    h
  )
    == Bool.pick(Maybe<&2, List<&2, U32>>, rc, Parts.get(d, h), None{}): Maybe<&2, List<&2, U32>>
} -> {
  Parts.get(
    Parts.only.add(g, x, acc),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      List.any.if(u => rc, c),
      Parts.get(d, h),
      None{}
    ): Maybe<&2, List<&2, U32>>
}:
  match g c acc:
    case None{} True{} acc:
      eg => ec => ih => Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Parts.get(acc, h),
        Bool.pick(Maybe<&2, List<&2, U32>>, rc, Parts.get(d, h), None{}),
        Parts.get(d, h),
        ih,
        Parts.pick_none(
          rc,
          Parts.get(d, h)
        )(Parts.get_at(d, x, h, None{})(Hashes.Hash.is_eq_sound(x, h)(ec))(eg))
      )
    case None{} False{} acc:
      eg => ec => ih => ih
    case Some{+ws} True{} Parts{t}:
      +eg => +ec => ih =>
        %Parts.get_set_of(
          t,
          Run.Parts.key(x),
          ws,
          Run.Parts.key(h),
          h
        ): {_ == Parts.get(d, h): Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Run.Parts.get.of(
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)),
              Some{ws},
              Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h))
            ),
            h
          ),
          Some{ws},
          Parts.get(d, h),
          Parts.set_hit(
            Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)),
            Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h)),
            ws,
            h
          )(
            Parts.key_same(x, h)(Hashes.Hash.is_eq_sound(x, h)(ec))
          )(
            Parts.heq_of(
              Hashes.Sha.hash(ws),
              h
            )(
              Parts.part_is(
                d,
                h,
                ws
              )(Parts.get_at(d, x, h, Some{ws})(Hashes.Hash.is_eq_sound(x, h)(ec))(eg))
            )
          ),
          Equal.sym(
            Maybe<&2, List<&2, U32>>,
            Parts.get(d, h),
            Some{ws},
            Parts.get_at(d, x, h, Some{ws})(Hashes.Hash.is_eq_sound(x, h)(ec))(eg)
          )
        )
    case Some{+ws} False{} Parts{t}:
      eg => ec => ih =>
        %Parts.get_set_of(
          t,
          Run.Parts.key(x),
          ws,
          Run.Parts.key(h),
          h
        ): {
          _
            == Bool.pick(
              Maybe<&2, List<&2, U32>>,
              rc,
              Parts.get(d, h),
              None{}
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Bool,
          Crits.Key.is_eq(Run.Parts.key(h), Run.Parts.key(x)),
          False{},
          Parts.key_ne(x, h)(ec)
        ): {
          Run.Parts.get.of(
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              _,
              Some{ws},
              Crits.Dict.get(List<&2, U32>, t, Run.Parts.key(h))
            ),
            h
          )
            == Bool.pick(
              Maybe<&2, List<&2, U32>>,
              rc,
              Parts.get(d, h),
              None{}
            ): Maybe<&2, List<&2, U32>>
        }
        ih
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the parts of d with a hash in hs hold what d holds under a hash of hs, and nothing else
def Parts.get_only_go(
  hs: List<&2, Hashes.Hash>,
  +d: Parts,
  +h: Hashes.Hash
) -> {
  Parts.get(
    Parts.only.go(hs, d),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, hs, h),
      Parts.get(d, h),
      None{}
    ): Maybe<&2, List<&2, U32>>
}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Parts.get_only_go.at(
        Parts.get(d, x),
        Hashes.Hash.is_eq(x, h),
        Parts.only.go(r, d),
        x,
        h,
        d,
        List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h)
      )({==})({==})(Parts.get_only_go(r, d, h))

# the parts of d with a hash in hs hold what d holds under a hash of hs, and nothing else
def Parts.get_only(
  d: Parts,
  hs: List<&2, Hashes.Hash>,
  h: Hashes.Hash
) -> {
  Parts.get(
    Parts.only(d, hs),
    h
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, hs, h),
      Parts.get(d, h),
      None{}
    ): Maybe<&2, List<&2, U32>>
}:
  Parts.get_only_go(hs, d, h)

# Laws of the maps
# ----------------
# The code that runs holds the plain map of the parts (run/parts.bend) and
# builds no proof. What is read from the parts is what the code that runs
# reads from their map, and each def of the code that runs keeps the map well
# formed.

# the map of the parts d: what the code that runs holds
def Parts.crit(d: Parts) -> Run.Parts:
  match d:
    case Parts{t}:
      Run.Parts{Crits.Dict.crit(List<&2, U32>, t)}

# the parts of a plain map m that is well formed (w)
def Parts.of(m: Run.Parts, w: {Run.Parts.wf(m) == True{}: Bool}) -> Parts:
  match m:
    case Run.Parts{t}:
      Parts{(t, w)}

# the map of the parts of a map is the map
def Parts.of_crit(
  m: Run.Parts,
  w: {Run.Parts.wf(m) == True{}: Bool}
) -> {Parts.crit(Parts.of(m, w)) == m: Run.Parts}:
  match m:
    case Run.Parts{t}:
      {==}

# the words of a hash in the parts are those that the code that runs reads
def Parts.get_runs(
  d: Parts,
  +h: Hashes.Hash
) -> {Parts.get(d, h) == Run.Parts.get(Parts.crit(d), h): Maybe<&2, List<&2, U32>>}:
  match d:
    case Parts{Tuple{m, w}}:
      {==}

# the map of the seen keys with k, unless it was seen, is what the code that
# runs gives
def Parts.uniq.seen_runs(
  was: Bool,
  +m: Crits.Crit<Unit>,
  w: {Crits.Crit.wf(~Unit, m, 0n) == True{}: Bool},
  +k: List<&2, U32>
) -> {
  Crits.Dict.crit(
    Unit,
    Parts.uniq.seen(was, Tuple{m, w}, k)
  )
    == Run.Parts.uniq.seen(was, m, k): Crits.Crit<Unit>
}:
  match was:
    case True{}:
      {==}
    case False{}:
      {==}

# the hashes, each once, are those that the code that runs gives
def Parts.uniq_runs(
  hs: List<&2, Hashes.Hash>,
  seen: Crits.Dict(Unit)
) -> {
  Parts.uniq(hs, seen) == Run.Parts.uniq(hs, Crits.Dict.crit(Unit, seen)): List<&2, Hashes.Hash>
}:
  match hs seen:
    case Nil{} seen:
      {==}
    case Con{+h, +r} Tuple{+m, +w}:
      %Parts.uniq.seen_runs(
        Crits.Crit.has(Unit, m, Run.Parts.key(h)),
        m,
        w,
        Run.Parts.key(h)
      ): {
        Run.Parts.uniq.cons(
          Crits.Crit.has(Unit, m, Run.Parts.key(h)),
          h,
          Parts.uniq(
            r,
            Parts.uniq.seen(
              Crits.Crit.has(Unit, m, Run.Parts.key(h)),
              Tuple{m, w},
              Run.Parts.key(h)
            )
          )
        )
          == Run.Parts.uniq.cons(
            Crits.Crit.has(Unit, m, Run.Parts.key(h)),
            h,
            Run.Parts.uniq(r, _)
          ): List<&2, Hashes.Hash>
      }
      Equal.cong(
        List<&2, Hashes.Hash>,
        List<&2, Hashes.Hash>,
        x => Run.Parts.uniq.cons(Crits.Crit.has(Unit, m, Run.Parts.key(h)), h, x),
        Parts.uniq(
          r,
          Parts.uniq.seen(Crits.Crit.has(Unit, m, Run.Parts.key(h)), Tuple{m, w}, Run.Parts.key(h))
        ),
        Run.Parts.uniq(
          r,
          Crits.Dict.crit(
            Unit,
            Parts.uniq.seen(
              Crits.Crit.has(Unit, m, Run.Parts.key(h)),
              Tuple{m, w},
              Run.Parts.key(h)
            )
          )
        ),
        Parts.uniq_runs(
          r,
          Parts.uniq.seen(Crits.Crit.has(Unit, m, Run.Parts.key(h)), Tuple{m, w}, Run.Parts.key(h))
        )
      )

# the hashes held in the parts are those that the code that runs lists
def Parts.list_runs(
  d: Parts
) -> {Parts.list(d) == Run.Parts.list(Parts.crit(d)): List<&2, Hashes.Hash>}:
  match d:
    case Parts{Tuple{+m, w}}:
      Parts.uniq_runs(
        Run.Parts.list.go(Crits.Crit.entries(List<&2, U32>, m)),
        Crits.Dict.new(~Unit)
      )

# no part is well formed
def Plain.new_wf() -> {Run.Parts.wf(Run.Parts.new()) == True{}: Bool}:
  Crits.Crit.new_wf(~List<&2, U32>)

# words put under a hash, unless it is held, keep the parts well formed
def Plain.put.if_wf(
  held: Bool,
  d: Run.Parts,
  +h: Hashes.Hash,
  +ws: List<&2, U32>
) -> {
  Run.Parts.wf(d) == True{}: Bool
} -> {Run.Parts.wf(Run.Parts.put.if(held, d, h, ws)) == True{}: Bool}:
  match held d:
    case True{} d:
      w => w
    case False{} Run.Parts{+t}:
      w => Crits.Crit.upsert_wf(~List<&2, U32>, ~(a => b => b), t, Run.Parts.key(h), ws)(w)

# words put under their hash keep the parts well formed
def Plain.put.at_wf(
  +d: Run.Parts,
  +h: Hashes.Hash,
  +ws: List<&2, U32>
) -> {
  Run.Parts.wf(d) == True{}: Bool
} -> {Run.Parts.wf(Run.Parts.put.at(d, h, ws)) == True{}: Bool}:
  w => Plain.put.if_wf(Maybe.is_some(&2, List<&2, U32>, Run.Parts.get(d, h)), d, h, ws)(w)

# words put under their hash keep the parts well formed
def Plain.put_wf(
  +d: Run.Parts,
  +ws: List<&2, U32>
) -> {Run.Parts.wf(d) == True{}: Bool} -> {Run.Parts.wf(Run.Parts.put(d, ws)) == True{}: Bool}:
  w => Plain.put.at_wf(d, Hashes.Sha.hash(ws), ws)(w)

# words joined under their hash, when hit, keep the parts well formed
def Plain.join.add_wf(
  hit: Bool,
  +a: Run.Parts,
  +h: Hashes.Hash,
  +ws: List<&2, U32>
) -> {
  Run.Parts.wf(a) == True{}: Bool
} -> {Run.Parts.wf(Run.Parts.join.add(hit, a, h, ws)) == True{}: Bool}:
  match hit:
    case True{}:
      w => Plain.put.at_wf(a, h, ws)(w)
    case False{}:
      w => w

# the words of the entries es, joined, keep the parts well formed
def Plain.join.go_wf(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +a: Run.Parts
) -> {Run.Parts.wf(a) == True{}: Bool} -> {Run.Parts.wf(Run.Parts.join.go(es, a)) == True{}: Bool}:
  match es:
    case Nil{}:
      w => w
    case Con{Crits.Bind{+k, +ws}, r}:
      w => Plain.join.go_wf(
        r,
        Run.Parts.join.add(
          Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
          a,
          Hashes.Sha.hash(ws),
          ws
        )
      )(
        Plain.join.add_wf(
          Crits.Key.is_eq(k, Run.Parts.key(Hashes.Sha.hash(ws))),
          a,
          Hashes.Sha.hash(ws),
          ws
        )(w)
      )

# the parts of b joined to a keep the parts well formed
def Plain.join_wf(
  +a: Run.Parts,
  b: Run.Parts
) -> {Run.Parts.wf(a) == True{}: Bool} -> {Run.Parts.wf(Run.Parts.join(a, b)) == True{}: Bool}:
  match b:
    case Run.Parts{t}:
      w => Plain.join.go_wf(Crits.Crit.entries(List<&2, U32>, t), a)(w)

# words kept under a hash, if any, keep the parts well formed
def Plain.only.add_wf(
  m: Maybe<&2, List<&2, U32>>,
  +h: Hashes.Hash,
  acc: Run.Parts
) -> {
  Run.Parts.wf(acc) == True{}: Bool
} -> {Run.Parts.wf(Run.Parts.only.add(m, h, acc)) == True{}: Bool}:
  match m acc:
    case None{} acc:
      w => w
    case Some{+ws} Run.Parts{+t}:
      w => Crits.Crit.upsert_wf(~List<&2, U32>, ~(a => b => b), t, Run.Parts.key(h), ws)(w)

# the parts kept of d, those of the hashes hs, are well formed
def Plain.only.go_wf(
  hs: List<&2, Hashes.Hash>,
  +d: Run.Parts
) -> {Run.Parts.wf(Run.Parts.only.go(hs, d)) == True{}: Bool}:
  match hs:
    case Nil{}:
      Crits.Crit.new_wf(~List<&2, U32>)
    case Con{+h, +r}:
      Plain.only.add_wf(Run.Parts.get(d, h), h, Run.Parts.only.go(r, d))(Plain.only.go_wf(r, d))

# the parts kept of d, those of the hashes hs, are well formed
def Plain.only_wf(
  +d: Run.Parts,
  hs: List<&2, Hashes.Hash>
) -> {Run.Parts.wf(Run.Parts.only(d, hs)) == True{}: Bool}:
  Plain.only.go_wf(hs, d)
