import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./spec.bend as Spec
import ./types.bend as Types

# Owner groups, read from the versions of a store
# -----------------------------------------------
# The versions of a store are a list of entries, oldest first. A Group version
# sets the members of a group of the store, an Own version makes a group the
# owner of a line; the latest one counts.

# the request that made the version e
def Entry.request(e: Types.Entry) -> Spec.Request:
  match e:
    case Types.Entry{p, k}:
      match p:
        case Types.Pick{a, pins}:
          match a:
            case Types.Ask{i, q, r}:
              r

# the id of the request that made the version e
def Entry.id(e: Types.Entry) -> Ledgers.Id:
  match e:
    case Types.Entry{p, k}:
      match p:
        case Types.Pick{a, pins}:
          match a:
            case Types.Ask{i, q, r}:
              i

# that the version j of the list es was made by the request r
def Groups.At(es: List<&2, Types.Entry>, j: Nat, r: Spec.Request) -> Type:
  Exists(
    Types.Entry,
    e => {
      List.get(&2, Types.Entry, es, j) == Some{e}: Maybe<&2, Types.Entry>
    }
      & {Entry.request(e) == r: Spec.Request}
  )

# what a scan of the versions looks for: the Group versions of the group name
# of a store, or the Own versions of a line
type Seek is Data:
  Seek.Group{store: Hashes.Hash, name: String}
  Seek.Own{line: Ledgers.Line}

# whether r is a Group of the group g of the store s
def Seek.fits.group(r: Spec.Request, s: Hashes.Hash, g: String) -> Bool:
  match r:
    case Spec.Request.Group{s2, g2, ms}:
      Bool.and(Hashes.Hash.is_eq(s2, s), String.eq(g2, g))
    case o:
      False{}

# whether r is an Own of the line c
def Seek.fits.own(r: Spec.Request, c: Ledgers.Line) -> Bool:
  match r:
    case Spec.Request.Own{c2, g}:
      Ledgers.Line.is_eq(c2, c)
    case o:
      False{}

# whether the request r is one that q looks for
def Seek.fits(q: Seek, r: Spec.Request) -> Bool:
  match q:
    case Seek.Group{s, g}:
      Seek.fits.group(r, s, g)
    case Seek.Own{c}:
      Seek.fits.own(r, c)

# r when it was a hit, else none
def Seek.if(hit: Bool, r: Spec.Request) -> Maybe<&2, Spec.Request>:
  match hit:
    case False{}:
      None{}
    case True{}:
      Some{r}

# the request r when q looks for it
def Seek.hit(q: Seek, +r: Spec.Request) -> Maybe<&2, Spec.Request>:
  Seek.if(Seek.fits(q, r), r)

# the request of the latest version of es that q looks for
def Groups.scan(es: List<&2, Types.Entry>, +q: Seek) -> Maybe<&2, Spec.Request>:
  match es:
    case Nil{}:
      None{}
    case Con{e, t}:
      Maybe.or(&2, Spec.Request, Groups.scan(t, q), Seek.hit(q, Entry.request(e)))

# that the version j of es was made by r, which q looks for
def Groups.Hit(es: List<&2, Types.Entry>, q: Seek, r: Spec.Request, j: Nat) -> Type:
  Groups.At(es, j, r) & {Seek.fits(q, r) == True{}: Bool}

# that no version of es after j is one that q looks for
def Groups.Later(es: List<&2, Types.Entry>, q: Seek, j: Nat) -> Type:
  @j2: Nat -> @r2: Spec.Request -> Groups.At(
    es,
    j2,
    r2
  ) -> {Seek.fits(q, r2) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}

# that r is the request of the latest version of es that q looks for
def Groups.Last(es: List<&2, Types.Entry>, q: Seek, r: Spec.Request) -> Type:
  Exists(Nat, j => Groups.Hit(es, q, r, j) & Groups.Later(es, q, j))

# a hit gives its request, and the request fits
def Seek.if_some(
  hit: Bool,
  r0: Spec.Request,
  r: Spec.Request
) -> {
  Seek.if(hit, r0) == Some{r}: Maybe<&2, Spec.Request>
} -> {hit == True{}: Bool}
  & {r0 == r: Spec.Request}:
  match hit:
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool} & {r0 == r: Spec.Request},
        Shared.Maybe.none_ne_some(Spec.Request, r, h)
      )
    case True{}:
      h => ({==}, Shared.Maybe.some_inj(Spec.Request, r0, r, h))

# no version is at an index of the empty list
def Groups.At.nil(-j: Nat, -r: Spec.Request, a: Groups.At([], j, r)) -> Empty:
  (e, p) = a
  (g, q) = p
  Shared.Maybe.none_ne_some(Types.Entry, e, g)

# both sides of a Maybe.or that is none are none
def Maybe.or_none_both(
  -A: Data,
  a: Maybe<&2, A>,
  b: Maybe<&2, A>
) -> {
  Maybe.or(&2, A, a, b) == None{}: Maybe<&2, A>
} -> {a == None{}: Maybe<&2, A>}
  & {b == None{}: Maybe<&2, A>}:
  match a:
    case None{}:
      h => ({==}, h)
    case Some{x}:
      h => Empty.absurd(
        {Some{x} == None{}: Maybe<&2, A>} & {b == None{}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, h))
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a request that fits is not a miss
def Seek.hit_fits(
  q: Seek,
  r: Spec.Request,
  f: {Seek.fits(q, r) == True{}: Bool},
  h: {Seek.hit(q, r) == None{}: Maybe<&2, Spec.Request>}
) -> Empty:
  Shared.Maybe.none_ne_some(
    Spec.Request,
    r,
    Equal.sym(
      Maybe<&2, Spec.Request>,
      Some{r},
      None{},
      (%f: {Seek.if(_, r) == None{}: Maybe<&2, Spec.Request>}
        h)
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# what follows from a witness and its fact follows from that there is one
def Exists.use(-A: Type, -B: @-x: A -> Type, -C: Type, p: Exists(A, B), k: @x: A -> B(x) -> C) -> C:
  (x, b) = p
  k(x)(b)

# what follows from two facts follows from their pair
def Pair.use(-A: Type, -B: Type, -C: Type, p: A & B, k: A -> B -> C) -> C:
  (a, b) = p
  k(a)(b)

# a scan that finds nothing: no version of es is one that q looks for
def Groups.scan_none(
  es: List<&2, Types.Entry>,
  j2: Nat,
  +q: Seek,
  +r2: Spec.Request,
  +h: {Groups.scan(es, q) == None{}: Maybe<&2, Spec.Request>},
  a: Groups.At(es, j2, r2),
  +f: {Seek.fits(q, r2) == True{}: Bool}
) -> Empty:
  match es j2:
    case Nil{} j:
      Groups.At.nil(j, r2, a)
    case Con{+e, +t} 0n:
      (+e0, p) = a
      (g, k) = p
      Seek.hit_fits(
        q,
        Entry.request(e),
        (%Equal.sym(
          Types.Entry,
          e,
          e0,
          Shared.Maybe.some_inj(Types.Entry, e, e0, g)
        ): {Seek.fits(q, Entry.request(_)) == True{}: Bool}
          %Equal.sym(Spec.Request, Entry.request(e0), r2, k): {Seek.fits(q, _) == True{}: Bool}
          f),
        Pair.snd(
          {Groups.scan(t, q) == None{}: Maybe<&2, Spec.Request>},
          {Seek.hit(q, Entry.request(e)) == None{}: Maybe<&2, Spec.Request>},
          Maybe.or_none_both(Spec.Request, Groups.scan(t, q), Seek.hit(q, Entry.request(e)))(h)
        )
      )
    case Con{+e, +t} 1n+p:
      Groups.scan_none(
        t,
        p,
        q,
        r2,
        Pair.fst(
          {Groups.scan(t, q) == None{}: Maybe<&2, Spec.Request>},
          {Seek.hit(q, Entry.request(e)) == None{}: Maybe<&2, Spec.Request>},
          Maybe.or_none_both(Spec.Request, Groups.scan(t, q), Seek.hit(q, Entry.request(e)))(h)
        ),
        a,
        f
      )

# no version after 1n+j fits, when none after j does in the tail
def Groups.Later.cons(
  j2: Nat,
  -j: Nat,
  -e: Types.Entry,
  -t: List<&2, Types.Entry>,
  -q: Seek,
  r2: Spec.Request,
  later: Groups.Later(t, q, j),
  a: Groups.At(e <> t, j2, r2),
  f: {Seek.fits(q, r2) == True{}: Bool}
) -> {Nat.is_le(j2, 1n+j) == True{}: Bool}:
  match j2:
    case 0n:
      {==}
    case 1n+p:
      later(p)(r2)(a)(f)

# no version after the first fits, when none of the tail does
def Groups.Later.first(
  j2: Nat,
  -e: Types.Entry,
  t: List<&2, Types.Entry>,
  q: Seek,
  r2: Spec.Request,
  none: {Groups.scan(t, q) == None{}: Maybe<&2, Spec.Request>},
  a: Groups.At(e <> t, j2, r2),
  f: {Seek.fits(q, r2) == True{}: Bool}
) -> {Nat.is_le(j2, 0n) == True{}: Bool}:
  match j2:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Groups.scan_none(t, p, q, r2, none, a, f))

# Groups.scan_last for e <> t, by what the scan of t gave (st)
def Groups.scan_last.at(
  +e: Types.Entry,
  +t: List<&2, Types.Entry>,
  +q: Seek,
  +r: Spec.Request,
  st: Maybe<&2, Spec.Request>,
  ih: @r2: Spec.Request -> {st == Some{r2}: Maybe<&2, Spec.Request>} -> Groups.Last(t, q, r2),
  no: {
    st == None{}: Maybe<&2, Spec.Request>
  } -> {Groups.scan(t, q) == None{}: Maybe<&2, Spec.Request>},
  h: {
    Maybe.or(
      &2,
      Spec.Request,
      st,
      Seek.hit(q, Entry.request(e))
    )
      == Some{r}: Maybe<&2, Spec.Request>
  }
) -> Groups.Last(e <> t, q, r):
  match st:
    case Some{+x}:
      %Shared.Maybe.some_inj(Spec.Request, x, r, h): Groups.Last(e <> t, q, _)
      Exists.use(
        Nat,
        j => Groups.Hit(t, q, x, j) & Groups.Later(t, q, j),
        Groups.Last(e <> t, q, x),
        ih(x)({==}),
        +j => body => Pair.use(
          Groups.Hit(t, q, x, j),
          Groups.Later(t, q, j),
          Groups.Last(e <> t, q, x),
          body,
          first => later => (
            1n+j,
            (first, j2 => r2 => a => f => Groups.Later.cons(j2, j, e, t, q, r2, later, a, f))
          )
        )
      )
    case None{}:
      Pair.use(
        {Seek.fits(q, Entry.request(e)) == True{}: Bool},
        {Entry.request(e) == r: Spec.Request},
        Groups.Last(e <> t, q, r),
        Seek.if_some(Seek.fits(q, Entry.request(e)), Entry.request(e), r)(h),
        hf => +hr => (0n, (((e, ({==}, hr)), (%hr: {Seek.fits(q, _) == True{}: Bool}
                hf)), j2 => r2 => a => f => Groups.Later.first(j2, e, t, q, r2, no({==}), a, f)))
      )

# what a scan finds is the request of the latest version that q looks for
def Groups.scan_last(
  es: List<&2, Types.Entry>,
  +q: Seek,
  +r: Spec.Request,
  h: {Groups.scan(es, q) == Some{r}: Maybe<&2, Spec.Request>}
) -> Groups.Last(es, q, r):
  match es:
    case Nil{}:
      Empty.absurd(Groups.Last([], q, r), Shared.Maybe.none_ne_some(Spec.Request, r, h))
    case Con{+e, +t}:
      Groups.scan_last.at(
        e,
        t,
        q,
        r,
        Groups.scan(t, q),
        r2 => h2 => Groups.scan_last(t, q, r2, h2),
        h0 => h0,
        h
      )

# an index of the first 1n+m elements of xs is an index of xs, at most m
def List.take_get(
  -A: Data,
  xs: List<&2, A>,
  j: Nat,
  m: Nat,
  -e: A,
  h: {List.get(&2, A, List.take(&2, A, xs, 1n+m), j) == Some{e}: Maybe<&2, A>}
) -> {List.get(&2, A, xs, j) == Some{e}: Maybe<&2, A>}
  & {Nat.is_le(j, m) == True{}: Bool}:
  match xs j m:
    case Nil{} j m:
      Empty.absurd(
        {List.get(&2, A, [], j) == Some{e}: Maybe<&2, A>} & {Nat.is_le(j, m) == True{}: Bool},
        Shared.Maybe.none_ne_some(A, e, h)
      )
    case Con{x, t} 0n m:
      (h, Shared.Nat.le_zero(m))
    case Con{x, t} 1n+p 0n:
      Empty.absurd(
        {List.get(&2, A, t, p) == Some{e}: Maybe<&2, A>} & {Nat.is_le(1n+p, 0n) == True{}: Bool},
        Shared.Maybe.none_ne_some(
          A,
          e,
          (%Shared.List.take_zero(A, t): {List.get(&2, A, _, p) == Some{e}: Maybe<&2, A>}
            h)
        )
      )
    case Con{x, t} 1n+p 1n+k:
      List.take_get(A, t, p, k, e, h)

# an index of xs that is at most m is an index of its first 1n+m elements
def List.get_take(
  -A: Data,
  xs: List<&2, A>,
  j: Nat,
  m: Nat,
  -e: A,
  h: {List.get(&2, A, xs, j) == Some{e}: Maybe<&2, A>},
  l: {Nat.is_le(j, m) == True{}: Bool}
) -> {List.get(&2, A, List.take(&2, A, xs, 1n+m), j) == Some{e}: Maybe<&2, A>}:
  match xs j m:
    case Nil{} j m:
      h
    case Con{x, t} 0n m:
      h
    case Con{x, t} 1n+p 0n:
      Empty.absurd(
        {List.get(&2, A, List.take(&2, A, t, 0n), p) == Some{e}: Maybe<&2, A>},
        Shared.Bool.false_ne_true(l)
      )
    case Con{x, t} 1n+p 1n+k:
      List.get_take(A, t, p, k, e, h, l)

# a version of the first 1n+m versions of store is a version of store, at most m
def Groups.At.of_take(
  +store: List<&2, Types.Entry>,
  +j: Nat,
  +m: Nat,
  -r: Spec.Request,
  a: Groups.At(List.take(&2, Types.Entry, store, 1n+m), j, r)
) -> Groups.At(store, j, r)
  & {Nat.is_le(j, m) == True{}: Bool}:
  (+e, p) = a
  (+g, k) = p
  (
    (
      e,
      (
        Pair.fst(
          {List.get(&2, Types.Entry, store, j) == Some{e}: Maybe<&2, Types.Entry>},
          {Nat.is_le(j, m) == True{}: Bool},
          List.take_get(Types.Entry, store, j, m, e, g)
        ),
        k
      )
    ),
    Pair.snd(
      {List.get(&2, Types.Entry, store, j) == Some{e}: Maybe<&2, Types.Entry>},
      {Nat.is_le(j, m) == True{}: Bool},
      List.take_get(Types.Entry, store, j, m, e, g)
    )
  )

# a version of store that is at most m is a version of its first 1n+m versions
def Groups.At.to_take(
  store: List<&2, Types.Entry>,
  j: Nat,
  m: Nat,
  -r: Spec.Request,
  a: Groups.At(store, j, r),
  l: {Nat.is_le(j, m) == True{}: Bool}
) -> Groups.At(List.take(&2, Types.Entry, store, 1n+m), j, r):
  (e, p) = a
  (g, k) = p
  (e, (List.get_take(Types.Entry, store, j, m, e, g, l), k))

# what holds of every Group of the group g of the store s holds of a request
# that fits it
def Seek.group_elim(
  -C: Spec.Request -> Type,
  r: Spec.Request,
  +s: Hashes.Hash,
  +g: String,
  +fit: {Seek.fits.group(r, s, g) == True{}: Bool},
  k: @ms: List<&2, String> -> C(Spec.Request.Group{s, g, ms})
) -> C(r):
  match r:
    case Spec.Request.Start{o}:
      Empty.absurd(C(Spec.Request.Start{o}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Write{b, p, w}:
      Empty.absurd(C(Spec.Request.Write{b, p, w}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Merge{f, i}:
      Empty.absurd(C(Spec.Request.Merge{f, i}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Resolve{i, p, w}:
      Empty.absurd(C(Spec.Request.Resolve{i, p, w}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Mark{b, n, v}:
      Empty.absurd(C(Spec.Request.Mark{b, n, v}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Move{b, t, v}:
      Empty.absurd(C(Spec.Request.Move{b, t, v}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Own{c2, g2}:
      Empty.absurd(C(Spec.Request.Own{c2, g2}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Group{+s2, +g2, +ms}:
      %Equal.sym(
        Hashes.Hash,
        s2,
        s,
        Hashes.Hash.is_eq_sound(
          s2,
          s
        )(Shared.Bool.and_true_left(Hashes.Hash.is_eq(s2, s), String.eq(g2, g))(fit))
      ): C(Spec.Request.Group{_, g2, ms})
      %Equal.sym(
        String,
        g2,
        g,
        Texts.String.eq_sound(
          g2,
          g
        )(Shared.Bool.and_true_right(Hashes.Hash.is_eq(s2, s), String.eq(g2, g))(fit))
      ): C(Spec.Request.Group{s, _, ms})
      k(ms)

# what holds of every Own of the line c holds of a request that fits it
def Seek.own_elim(
  -C: Spec.Request -> Type,
  r: Spec.Request,
  +c: Ledgers.Line,
  +fit: {Seek.fits.own(r, c) == True{}: Bool},
  k: @g: String -> C(Spec.Request.Own{c, g})
) -> C(r):
  match r:
    case Spec.Request.Start{o}:
      Empty.absurd(C(Spec.Request.Start{o}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Write{b, p, w}:
      Empty.absurd(C(Spec.Request.Write{b, p, w}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Merge{f, i}:
      Empty.absurd(C(Spec.Request.Merge{f, i}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Resolve{i, p, w}:
      Empty.absurd(C(Spec.Request.Resolve{i, p, w}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Mark{b, n, v}:
      Empty.absurd(C(Spec.Request.Mark{b, n, v}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Move{b, t, v}:
      Empty.absurd(C(Spec.Request.Move{b, t, v}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Group{s2, g2, ms}:
      Empty.absurd(C(Spec.Request.Group{s2, g2, ms}), Shared.Bool.false_ne_true(fit))
    case Spec.Request.Own{+c2, +g2}:
      %Equal.sym(
        Ledgers.Line,
        c2,
        c,
        Ledgers.Line.is_eq_sound(c2, c)(fit)
      ): C(Spec.Request.Own{_, g2})
      k(g2)

# a Group of the group g of the store s fits the scan for it
def Seek.group_refl(
  +s: Hashes.Hash,
  +g: String
) -> {Bool.and(Hashes.Hash.is_eq(s, s), String.eq(g, g)) == True{}: Bool}:
  Shared.Bool.and_both(
    Hashes.Hash.is_eq(s, s),
    String.eq(g, g)
  )(Hashes.Hash.is_eq_refl(s))(Texts.String.eq_refl(g))

# the members that a request sets (none: it is no Group)
def Request.members(r: Spec.Request) -> Maybe<&2, List<&2, String>>:
  match r:
    case Spec.Request.Group{s, g, ms}:
      Some{ms}
    case o:
      None{}

# the owner group that a request sets (none: it is no Own)
def Request.group(r: Spec.Request) -> Maybe<&2, String>:
  match r:
    case Spec.Request.Own{c, g}:
      Some{g}
    case o:
      None{}

# the members that a found request sets
def Seek.members(st: Maybe<&2, Spec.Request>) -> Maybe<&2, List<&2, String>>:
  match st:
    case None{}:
      None{}
    case Some{r}:
      Request.members(r)

# the owner group that a found request sets
def Seek.group(st: Maybe<&2, Spec.Request>) -> Maybe<&2, String>:
  match st:
    case None{}:
      None{}
    case Some{r}:
      Request.group(r)

# the members of the group g of the store s, by the versions es (none: g is
# no group)
def Groups.mem(es: List<&2, Types.Entry>, s: Hashes.Hash, g: String) -> Maybe<&2, List<&2, String>>:
  Seek.members(Groups.scan(es, Seek.Group{s, g}))

# the owner group of the line c, by the versions es (none: none was set)
def Groups.own(es: List<&2, Types.Entry>, c: Ledgers.Line) -> Maybe<&2, String>:
  Seek.group(Groups.scan(es, Seek.Own{c}))

# the latest request that q looks for is r2, when it is r, equal to r2
def Groups.Last.cast.to(
  -es: List<&2, Types.Entry>,
  -q: Seek,
  -r: Spec.Request,
  -r2: Spec.Request,
  e: {r == r2: Spec.Request},
  l: Groups.Last(es, q, r)
) -> Groups.Last(es, q, r2):
  %e: Groups.Last(es, q, _)
  l

# Groups.Last.cast, from the parts of its premise
def Groups.Last.cast.of(
  -es: List<&2, Types.Entry>,
  -q: Seek,
  -r: Spec.Request,
  -r2: Spec.Request,
  j: Nat,
  at: Groups.At(es, j, r),
  +fit: {Seek.fits(q, r) == True{}: Bool},
  later: Groups.Later(es, q, j),
  k: {Seek.fits(q, r) == True{}: Bool} -> {r == r2: Spec.Request}
) -> Groups.Last(es, q, r2):
  Groups.Last.cast.to(es, q, r, r2, k(fit), (j, ((at, fit), later)))

# the latest request that q looks for is r2, when being one makes r equal r2
def Groups.Last.cast(
  -es: List<&2, Types.Entry>,
  -q: Seek,
  -r: Spec.Request,
  -r2: Spec.Request,
  l: Groups.Last(es, q, r),
  k: {Seek.fits(q, r) == True{}: Bool} -> {r == r2: Spec.Request}
) -> Groups.Last(es, q, r2):
  (j, body) = l
  (hit, later) = body
  (at, fit) = hit
  Groups.Last.cast.of(es, q, r, r2, j, at, fit, later, k)

# the latest request that q looks for is one that q looks for
def Groups.Last.fits(
  -es: List<&2, Types.Entry>,
  -q: Seek,
  -r: Spec.Request,
  l: Groups.Last(es, q, r)
) -> {Seek.fits(q, r) == True{}: Bool}:
  (j, body) = l
  (hit, later) = body
  (at, fit) = hit
  fit

# Groups.mem_last, by what the scan gave (st)
def Groups.mem_last.at(
  -es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  st: Maybe<&2, Spec.Request>,
  ih: @r: Spec.Request -> {
    st == Some{r}: Maybe<&2, Spec.Request>
  } -> Groups.Last(es, Seek.Group{s, g}, r),
  +h: {Seek.members(st) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> Groups.Last(es, Seek.Group{s, g}, Spec.Request.Group{s, g, ms}):
  match st:
    case None{}:
      Empty.absurd(
        Groups.Last(es, Seek.Group{s, g}, Spec.Request.Group{s, g, ms}),
        Shared.Maybe.none_ne_some(List<&2, String>, ms, h)
      )
    case Some{+r}:
      Groups.Last.cast(
        es,
        Seek.Group{s, g},
        r,
        Spec.Request.Group{s, g, ms},
        ih(r)({==}),
        fit => Seek.group_elim(
          x => {Request.members(x) == Some{ms}: Maybe<&2, List<&2, String>>} -> {x == Spec.Request.Group{s, g, ms}: Spec.Request},
          r,
          s,
          g,
          fit,
          ms2 => h2 =>
            %Shared.Maybe.some_inj(List<&2, String>, ms2, ms, h2): {Spec.Request.Group{s, g, ms2} == Spec.Request.Group{s, g, _}: Spec.Request}
            {==})(h)
      )

# the members of a group are those of its latest Group version
def Groups.mem_last(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  h: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> Groups.Last(es, Seek.Group{s, g}, Spec.Request.Group{s, g, ms}):
  Groups.mem_last.at(
    es,
    s,
    g,
    ms,
    Groups.scan(es, Seek.Group{s, g}),
    r => h2 => Groups.scan_last(es, Seek.Group{s, g}, r, h2),
    h
  )

# Groups.own_last, by what the scan gave (st)
def Groups.own_last.at(
  -es: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +g: String,
  st: Maybe<&2, Spec.Request>,
  ih: @r: Spec.Request -> {
    st == Some{r}: Maybe<&2, Spec.Request>
  } -> Groups.Last(es, Seek.Own{c}, r),
  +h: {Seek.group(st) == Some{g}: Maybe<&2, String>}
) -> Groups.Last(es, Seek.Own{c}, Spec.Request.Own{c, g}):
  match st:
    case None{}:
      Empty.absurd(
        Groups.Last(es, Seek.Own{c}, Spec.Request.Own{c, g}),
        Shared.Maybe.none_ne_some(String, g, h)
      )
    case Some{+r}:
      Groups.Last.cast(
        es,
        Seek.Own{c},
        r,
        Spec.Request.Own{c, g},
        ih(r)({==}),
        fit => Seek.own_elim(
          x => {Request.group(x) == Some{g}: Maybe<&2, String>} -> {x == Spec.Request.Own{c, g}: Spec.Request},
          r,
          c,
          fit,
          g2 => h2 =>
            %Shared.Maybe.some_inj(String, g2, g, h2): {Spec.Request.Own{c, g2} == Spec.Request.Own{c, _}: Spec.Request}
            {==})(h)
      )

# the owner group of a line is that of its latest Own version
def Groups.own_last(
  +es: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +g: String,
  h: {Groups.own(es, c) == Some{g}: Maybe<&2, String>}
) -> Groups.Last(es, Seek.Own{c}, Spec.Request.Own{c, g}):
  Groups.own_last.at(
    es,
    c,
    g,
    Groups.scan(es, Seek.Own{c}),
    r => h2 => Groups.scan_last(es, Seek.Own{c}, r, h2),
    h
  )

# Groups.mem_of_at, by what the scan gave (st)
def Groups.mem_of_at.at(
  +s: Hashes.Hash,
  +g: String,
  st: Maybe<&2, Spec.Request>,
  none: {st == None{}: Maybe<&2, Spec.Request>} -> Empty,
  fit: @r: Spec.Request -> {
    st == Some{r}: Maybe<&2, Spec.Request>
  } -> {Seek.fits.group(r, s, g) == True{}: Bool}
) -> Exists(List<&2, String>, ms2 => {Seek.members(st) == Some{ms2}: Maybe<&2, List<&2, String>>}):
  match st:
    case None{}:
      Empty.absurd(
        Exists(List<&2, String>, ms2 => {None{} == Some{ms2}: Maybe<&2, List<&2, String>>}),
        none({==})
      )
    case Some{+r}:
      Seek.group_elim(
        x => Exists(
          List<&2, String>,
          ms2 => {Request.members(x) == Some{ms2}: Maybe<&2, List<&2, String>>}
        ),
        r,
        s,
        g,
        fit(r)({==}),
        ms2 => (ms2, {==})
      )

# a name with a Group version is a group
def Groups.mem_of_at(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +j: Nat,
  +ms: List<&2, String>,
  a: Groups.At(es, j, Spec.Request.Group{s, g, ms})
) -> Exists(
  List<&2, String>,
  ms2 => {Groups.mem(es, s, g) == Some{ms2}: Maybe<&2, List<&2, String>>}
):
  Groups.mem_of_at.at(
    s,
    g,
    Groups.scan(es, Seek.Group{s, g}),
    h0 => Groups.scan_none(
      es,
      j,
      Seek.Group{s, g},
      Spec.Request.Group{s, g, ms},
      h0,
      a,
      Seek.group_refl(s, g)
    ),
    r => h1 => Groups.Last.fits(
      es,
      Seek.Group{s, g},
      r,
      Groups.scan_last(es, Seek.Group{s, g}, r, h1)
    )
  )

# the members that were found, or none of them
def Groups.list(mv: Maybe<&2, List<&2, String>>) -> List<&2, String>:
  match mv:
    case None{}:
      []
    case Some{ms}:
      ms

# the nodes that the member v gives: itself when it is no group (mv is none),
# else the nodes of the group v (sub)
def Groups.part(
  mv: Maybe<&2, List<&2, String>>,
  v: String,
  sub: List<&2, String>
) -> List<&2, String>:
  match mv:
    case None{}:
      [v]
    case Some{ms}:
      sub

# the nodes of the members ms, by the versions es of the store s: those that
# are no groups, and for each that is a group, the nodes of its members, f
# groups deep
def Groups.walk(
  +f: Nat,
  ms: List<&2, String>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> List<&2, String>:
  match f ms:
    case 0n Nil{}:
      []
    case 0n Con{+v, t}:
      List.append(&2, String, Groups.part(Groups.mem(es, s, v), v, []), Groups.walk(0n, t, es, s))
    case 1n+p Nil{}:
      []
    case 1n+p Con{+v, t}:
      List.append(
        &2,
        String,
        Groups.part(
          Groups.mem(es, s, v),
          v,
          Groups.walk(p, Groups.list(Groups.mem(es, s, v)), es, s)
        ),
        Groups.walk(1n+p, t, es, s)
      )

# the nodes of the group g, f groups deep: N(f, g)
def Groups.reach(
  f: Nat,
  g: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> List<&2, String>:
  match f:
    case 0n:
      []
    case 1n+p:
      Groups.walk(p, Groups.list(Groups.mem(es, s, g)), es, s)

# the nodes of the members ms are those of the first, then those of the others
def Groups.walk_cons(
  f: Nat,
  v: String,
  t: List<&2, String>,
  es: List<&2, Types.Entry>,
  s: Hashes.Hash
) -> {
  Groups.walk(
    f,
    v <> t,
    es,
    s
  )
    == List.append(
      &2,
      String,
      Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
      Groups.walk(f, t, es, s)
    ): List<&2, String>
}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# no members give no nodes
def Groups.walk_nil(
  f: Nat,
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash
) -> {Groups.walk(f, [], es, s) == []: List<&2, String>}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a lazy "or" with a false rest is true only by its hit
def List.any.if_one(
  hit: Bool
) -> {List.any.if(u => False{}, hit) == True{}: Bool} -> {hit == True{}: Bool}:
  match hit:
    case False{}:
      h => h
    case True{}:
      h => {==}

# a list holds its first element
def Names.contains_first(
  +u: String,
  -t: List<&2, String>
) -> {List.contains(~String, ~String.eq, u <> t, u) == True{}: Bool}:
  %Equal.sym(
    Bool,
    String.eq(u, u),
    True{},
    Texts.String.eq_refl(u)
  ): {List.any.if(w => List.contains(~String, ~String.eq, t, u), _) == True{}: Bool}
  {==}

# Groups.walk_part at the first member u, by whether it is v (hit)
def Groups.walk_part.at(
  hit: Bool,
  +f: Nat,
  +u: String,
  +t: List<&2, String>,
  +v: String,
  +x: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  eqh: {String.eq(u, v) == hit: Bool},
  h1: {List.any.if(w => List.contains(~String, ~String.eq, t, v), hit) == True{}: Bool},
  h2: {
    List.contains(
      ~String,
      ~String.eq,
      Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
      x
    )
      == True{}: Bool
  },
  ih: {
    List.contains(~String, ~String.eq, t, v) == True{}: Bool
  } -> {List.contains(~String, ~String.eq, Groups.walk(f, t, es, s), x) == True{}: Bool}
) -> {
  List.contains(
    ~String,
    ~String.eq,
    List.append(
      &2,
      String,
      Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
      Groups.walk(f, t, es, s)
    ),
    x
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      Shared.List.contains_left(
        ~String,
        ~String.eq,
        Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
        Groups.walk(f, t, es, s),
        x,
        (%Equal.sym(
          String,
          u,
          v,
          Texts.String.eq_sound(u, v)(eqh)
        ): {
          List.contains(
            ~String,
            ~String.eq,
            Groups.part(Groups.mem(es, s, _), _, Groups.reach(f, _, es, s)),
            x
          )
            == True{}: Bool
        }
          h2)
      )
    case False{}:
      Shared.List.contains_right(
        ~String,
        ~String.eq,
        Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
        Groups.walk(f, t, es, s),
        x,
        ih(h1)
      )

# the nodes of the members ms hold what a member v of ms gives
def Groups.walk_part(
  ms: List<&2, String>,
  +f: Nat,
  +v: String,
  +x: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  h1: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  +h2: {
    List.contains(
      ~String,
      ~String.eq,
      Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
      x
    )
      == True{}: Bool
  }
) -> {List.contains(~String, ~String.eq, Groups.walk(f, ms, es, s), x) == True{}: Bool}:
  match ms:
    case Nil{}:
      Empty.absurd(
        {List.contains(~String, ~String.eq, Groups.walk(f, [], es, s), x) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Con{+u, +t}:
      %Equal.sym(
        List<&2, String>,
        Groups.walk(f, u <> t, es, s),
        List.append(
          &2,
          String,
          Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
          Groups.walk(f, t, es, s)
        ),
        Groups.walk_cons(f, u, t, es, s)
      ): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
      Groups.walk_part.at(
        String.eq(u, v),
        f,
        u,
        t,
        v,
        x,
        es,
        s,
        {==},
        h1,
        h2,
        h3 => Groups.walk_part(t, f, v, x, es, s, h3, h2)
      )

# Groups.walk_only at the first member u, by whether x is of what it gives (c)
def Groups.walk_only.at(
  c: Bool,
  -f: Nat,
  +u: String,
  +t: List<&2, String>,
  +x: String,
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  eqc: {
    List.contains(
      ~String,
      ~String.eq,
      Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
      x
    )
      == c: Bool
  },
  h: {Bool.or(c, List.contains(~String, ~String.eq, Groups.walk(f, t, es, s), x)) == True{}: Bool},
  ih: {
    List.contains(~String, ~String.eq, Groups.walk(f, t, es, s), x) == True{}: Bool
  } -> Exists(
    String,
    v => {
      List.contains(~String, ~String.eq, t, v) == True{}: Bool
    }
      & {
        List.contains(
          ~String,
          ~String.eq,
          Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
          x
        )
          == True{}: Bool
      }
  )
) -> Exists(
  String,
  v => {
    List.contains(~String, ~String.eq, u <> t, v) == True{}: Bool
  }
    & {
      List.contains(
        ~String,
        ~String.eq,
        Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
        x
      )
        == True{}: Bool
    }
):
  match c:
    case True{}:
      (u, (Names.contains_first(u, t), eqc))
    case False{}:
      Exists.use(
        String,
        v => {
          List.contains(~String, ~String.eq, t, v) == True{}: Bool
        }
          & {
            List.contains(
              ~String,
              ~String.eq,
              Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
              x
            )
              == True{}: Bool
          },
        Exists(
          String,
          v => {
            List.contains(~String, ~String.eq, u <> t, v) == True{}: Bool
          }
            & {
              List.contains(
                ~String,
                ~String.eq,
                Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
                x
              )
                == True{}: Bool
            }
        ),
        ih(h),
        +v => body => Pair.use(
          {List.contains(~String, ~String.eq, t, v) == True{}: Bool},
          {
            List.contains(
              ~String,
              ~String.eq,
              Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
              x
            )
              == True{}: Bool
          },
          Exists(
            String,
            v2 => {
              List.contains(~String, ~String.eq, u <> t, v2) == True{}: Bool
            }
              & {
                List.contains(
                  ~String,
                  ~String.eq,
                  Groups.part(Groups.mem(es, s, v2), v2, Groups.reach(f, v2, es, s)),
                  x
                )
                  == True{}: Bool
              }
          ),
          body,
          b1 => b2 => (v, (Shared.List.contains_cons(~String, ~String.eq, u, t, v)(b1), b2))
        )
      )

# what the nodes of the members ms hold, a member of ms gives
def Groups.walk_only(
  ms: List<&2, String>,
  +f: Nat,
  +x: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  h: {List.contains(~String, ~String.eq, Groups.walk(f, ms, es, s), x) == True{}: Bool}
) -> Exists(
  String,
  v => {
    List.contains(~String, ~String.eq, ms, v) == True{}: Bool
  }
    & {
      List.contains(
        ~String,
        ~String.eq,
        Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
        x
      )
        == True{}: Bool
    }
):
  match ms:
    case Nil{}:
      Empty.absurd(
        Exists(
          String,
          v => {
            List.contains(~String, ~String.eq, [], v) == True{}: Bool
          }
            & {
              List.contains(
                ~String,
                ~String.eq,
                Groups.part(Groups.mem(es, s, v), v, Groups.reach(f, v, es, s)),
                x
              )
                == True{}: Bool
            }
        ),
        Shared.Bool.false_ne_true(
          (%Groups.walk_nil(f, es, s): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
            h)
        )
      )
    case Con{+u, +t}:
      Groups.walk_only.at(
        List.contains(
          ~String,
          ~String.eq,
          Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
          x
        ),
        f,
        u,
        t,
        x,
        es,
        s,
        {==},
        (%Shared.List.contains_append(
          ~String,
          ~String.eq,
          Groups.part(Groups.mem(es, s, u), u, Groups.reach(f, u, es, s)),
          Groups.walk(f, t, es, s),
          x
        ): {_ == True{}: Bool}
          %Groups.walk_cons(
          f,
          u,
          t,
          es,
          s
        ): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
          h),
        h3 => Groups.walk_only(t, f, x, es, s, h3)
      )

# Names.within_contains at the first name p, by whether it is x (hit)
def Names.within_contains.at(
  hit: Bool,
  +p: String,
  -r: List<&2, String>,
  -ks: List<&2, String>,
  +x: String,
  eqh: {String.eq(p, x) == hit: Bool},
  h2: {List.any.if(w => List.contains(~String, ~String.eq, r, x), hit) == True{}: Bool},
  hp: {List.contains(~String, ~String.eq, ks, p) == True{}: Bool},
  ih: {
    List.contains(~String, ~String.eq, r, x) == True{}: Bool
  } -> {List.contains(~String, ~String.eq, ks, x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, ks, x) == True{}: Bool}:
  match hit:
    case True{}:
      %Texts.String.eq_sound(p, x)(eqh): {List.contains(~String, ~String.eq, ks, _) == True{}: Bool}
      hp
    case False{}:
      ih(h2)

# a list whose names are all in ks holds only names of ks
def Names.within_contains(
  ps: List<&2, String>,
  +ks: List<&2, String>,
  +x: String,
  +h1: {Shared.List.within(~String, ~String.eq, ps, ks) == True{}: Bool},
  h2: {List.contains(~String, ~String.eq, ps, x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, ks, x) == True{}: Bool}:
  match ps:
    case Nil{}:
      Empty.absurd(
        {List.contains(~String, ~String.eq, ks, x) == True{}: Bool},
        Shared.Bool.false_ne_true(h2)
      )
    case Con{+p, +r}:
      Names.within_contains.at(
        String.eq(p, x),
        p,
        r,
        ks,
        x,
        {==},
        h2,
        Shared.Bool.and_true_left(
          List.contains(~String, ~String.eq, ks, p),
          Shared.List.within(~String, ~String.eq, r, ks)
        )(h1),
        h3 => Names.within_contains(
          r,
          ks,
          x,
          Shared.Bool.and_true_right(
            List.contains(~String, ~String.eq, ks, p),
            Shared.List.within(~String, ~String.eq, r, ks)
          )(h1),
          h3
        )
      )

# the names of xs, each once
def Groups.set(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+h, +t}:
      List.filter.put(String, h, Groups.set(t), Bool.not(List.contains(~String, ~String.eq, t, h)))

# Groups.set_keeps at the first name h, by whether the rest holds it (c) and
# whether it is x (e)
def Groups.set_keeps.at(
  c: Bool,
  e: Bool,
  +h: String,
  +t: List<&2, String>,
  +x: String,
  eqc: {List.contains(~String, ~String.eq, t, h) == c: Bool},
  eqe: {String.eq(h, x) == e: Bool},
  hx: {List.any.if(w => List.contains(~String, ~String.eq, t, x), e) == True{}: Bool},
  ih: {
    List.contains(~String, ~String.eq, t, x) == True{}: Bool
  } -> {List.contains(~String, ~String.eq, Groups.set(t), x) == True{}: Bool}
) -> {
  List.contains(
    ~String,
    ~String.eq,
    List.filter.put(String, h, Groups.set(t), Bool.not(c)),
    x
  )
    == True{}: Bool
}:
  match c e:
    case True{} True{}:
      ih(
        (%Texts.String.eq_sound(
          h,
          x
        )(eqe): {List.contains(~String, ~String.eq, t, _) == True{}: Bool}
          eqc)
      )
    case True{} False{}:
      ih(hx)
    case False{} True{}:
      %Equal.sym(
        Bool,
        String.eq(h, x),
        True{},
        eqe
      ): {List.any.if(w => List.contains(~String, ~String.eq, Groups.set(t), x), _) == True{}: Bool}
      {==}
    case False{} False{}:
      Shared.List.contains_cons(~String, ~String.eq, h, Groups.set(t), x)(ih(hx))

# the set of xs holds every name of xs
def Groups.set_keeps(
  xs: List<&2, String>,
  +x: String,
  hx: {List.contains(~String, ~String.eq, xs, x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, Groups.set(xs), x) == True{}: Bool}:
  match xs:
    case Nil{}:
      hx
    case Con{+h, +t}:
      Groups.set_keeps.at(
        List.contains(~String, ~String.eq, t, h),
        String.eq(h, x),
        h,
        t,
        x,
        {==},
        {==},
        hx,
        h3 => Groups.set_keeps(t, x, h3)
      )

# Groups.set_only at the first name h, by whether the rest holds it (c) and
# whether it is x (e)
def Groups.set_only.at(
  c: Bool,
  e: Bool,
  +h: String,
  +t: List<&2, String>,
  +x: String,
  eqe: {String.eq(h, x) == e: Bool},
  hd: {
    List.contains(
      ~String,
      ~String.eq,
      List.filter.put(String, h, Groups.set(t), Bool.not(c)),
      x
    )
      == True{}: Bool
  },
  ih: {
    List.contains(~String, ~String.eq, Groups.set(t), x) == True{}: Bool
  } -> {List.contains(~String, ~String.eq, t, x) == True{}: Bool}
) -> {List.any.if(w => List.contains(~String, ~String.eq, t, x), e) == True{}: Bool}:
  match c e:
    case True{} True{}:
      {==}
    case True{} False{}:
      ih(hd)
    case False{} True{}:
      {==}
    case False{} False{}:
      ih(
        (%eqe: {
          List.any.if(w => List.contains(~String, ~String.eq, Groups.set(t), x), _) == True{}: Bool
        }
          hd)
      )

# the set of xs holds only names of xs
def Groups.set_only(
  xs: List<&2, String>,
  +x: String,
  hd: {List.contains(~String, ~String.eq, Groups.set(xs), x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, xs, x) == True{}: Bool}:
  match xs:
    case Nil{}:
      hd
    case Con{+h, +t}:
      Groups.set_only.at(
        List.contains(~String, ~String.eq, t, h),
        String.eq(h, x),
        h,
        t,
        x,
        {==},
        hd,
        h3 => Groups.set_only(t, x, h3)
      )

# how many groups deep the nodes are read: more than the groups that the
# versions es can name
def Groups.fuel(es: List<&2, Types.Entry>) -> Nat:
  1n+1n+List.length(&2, Types.Entry, es)

# whether one more round leaves the nodes of the group g as they are
def Groups.same(+g: String, +es: List<&2, Types.Entry>, +s: Hashes.Hash) -> Bool:
  Shared.List.same_set(
    ~String,
    ~String.eq,
    Groups.reach(Groups.fuel(es), g, es, s),
    Groups.reach(1n+Groups.fuel(es), g, es, s)
  )

# whether the request r, when it is a Group of the store s, names a group
# whose nodes one more round leaves as they are
def Groups.stable.at(r: Spec.Request, +es: List<&2, Types.Entry>, +s: Hashes.Hash) -> Bool:
  match r:
    case Spec.Request.Group{s2, g, ms}:
      Bool.or(Bool.not(Hashes.Hash.is_eq(s2, s)), Groups.same(g, es, s))
    case o:
      True{}

# whether one more round leaves the nodes of every group of the store s that
# the versions rs name as they are, by the versions es
def Groups.stable(rs: List<&2, Types.Entry>, +es: List<&2, Types.Entry>, +s: Hashes.Hash) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Groups.stable.at(Entry.request(e), es, s), Groups.stable(t, es, s))

# whether the groups of the store s are good, by the versions es: the nodes of
# each are all that it reaches
def Groups.sound(+es: List<&2, Types.Entry>, +s: Hashes.Hash) -> Bool:
  Groups.stable(es, es, s)

# a stable Group of the store s itself names a group that is the same
def Groups.stable_at.fin(
  +s: Hashes.Hash,
  -g: String,
  -ms: List<&2, String>,
  -es: List<&2, Types.Entry>,
  h: {Groups.stable.at(Spec.Request.Group{s, g, ms}, es, s) == True{}: Bool}
) -> {Groups.same(g, es, s) == True{}: Bool}:
  %Hashes.Hash.is_eq_refl(s): {Bool.or(Bool.not(_), Groups.same(g, es, s)) == True{}: Bool}
  h

# one more round leaves the nodes of a group with a Group version in rs as they are
def Groups.stable_at(
  rs: List<&2, Types.Entry>,
  j: Nat,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  h: {Groups.stable(rs, es, s) == True{}: Bool},
  a: Groups.At(rs, j, Spec.Request.Group{s, g, ms})
) -> {Groups.same(g, es, s) == True{}: Bool}:
  match rs j:
    case Nil{} j:
      Empty.absurd(
        {Groups.same(g, es, s) == True{}: Bool},
        Groups.At.nil(j, Spec.Request.Group{s, g, ms}, a)
      )
    case Con{+e, +t} 0n:
      (+e0, p) = a
      (ge, k) = p
      Groups.stable_at.fin(s, g, ms, es, (%k: {Groups.stable.at(_, es, s) == True{}: Bool}
          %Shared.Maybe.some_inj(Types.Entry, e, e0, ge): {Groups.stable.at(Entry.request(_), es, s) == True{}: Bool}
          Shared.Bool.and_true_left(Groups.stable.at(Entry.request(e), es, s), Groups.stable(t, es, s))(h)))
    case Con{+e, +t} 1n+p:
      Groups.stable_at(
        t,
        p,
        es,
        s,
        g,
        ms,
        Shared.Bool.and_true_right(
          Groups.stable.at(Entry.request(e), es, s),
          Groups.stable(t, es, s)
        )(h),
        a
      )

# the version of the latest request that q looks for
def Groups.Last.at(
  -es: List<&2, Types.Entry>,
  -q: Seek,
  -r: Spec.Request,
  l: Groups.Last(es, q, r)
) -> Exists(Nat, j => Groups.At(es, j, r)):
  (j, body) = l
  (hit, later) = body
  (at, fit) = hit
  (j, at)

# when the groups are good, one more round leaves the nodes of a group as they are
def Groups.sound_same(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  hs: {Groups.sound(es, s) == True{}: Bool},
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {Groups.same(g, es, s) == True{}: Bool}:
  Exists.use(
    Nat,
    j => Groups.At(es, j, Spec.Request.Group{s, g, ms}),
    {Groups.same(g, es, s) == True{}: Bool},
    Groups.Last.at(
      es,
      Seek.Group{s, g},
      Spec.Request.Group{s, g, ms},
      Groups.mem_last(es, s, g, ms, hm)
    ),
    j => a => Groups.stable_at(es, j, es, s, g, ms, hs, a)
  )

# The reads
# ---------

# an answer that is given only when the groups are good (b)
def Groups.gate(-A: Data, b: Bool, m: Maybe<&2, A>) -> Maybe<&2, A>:
  match b:
    case False{}:
      None{}
    case True{}:
      m

# the members of the group g of the store s, by the versions es (none: g is
# no group, or the groups are not good)
def Groups.members.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String
) -> Maybe<&2, List<&2, String>>:
  Groups.gate(List<&2, String>, Groups.sound(es, s), Groups.mem(es, s, g))

# whether g is a group of the store s, by the versions es (none: the groups
# are not good)
def Groups.is_group.of(+es: List<&2, Types.Entry>, +s: Hashes.Hash, g: String) -> Maybe<&2, Bool>:
  Groups.gate(
    Bool,
    Groups.sound(es, s),
    Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, g))}
  )

# the nodes ns, when the name is a group (mv is its members)
def Groups.nodes.pick(
  mv: Maybe<&2, List<&2, String>>,
  ns: List<&2, String>
) -> Maybe<&2, List<&2, String>>:
  match mv:
    case None{}:
      None{}
    case Some{ms}:
      Some{ns}

# the nodes of the group g of the store s, by the versions es, each once
# (none: g is no group, or the groups are not good)
def Groups.nodes.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String
) -> Maybe<&2, List<&2, String>>:
  Groups.gate(
    List<&2, String>,
    Groups.sound(es, s),
    Groups.nodes.pick(Groups.mem(es, s, g), Groups.set(Groups.reach(Groups.fuel(es), g, es, s)))
  )

# whether the groups of the store s are good at the version m of r: the nodes
# of each group are all that it reaches
def Groups.good(r: List<&2, Types.Entry>, +s: Hashes.Hash, m: Nat) -> Bool:
  Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s)

# the members of the group g of the store s at the version m of r (none: g is
# no group, or the groups are not good)
def Groups.members(
  r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String,
  m: Nat
) -> Maybe<&2, List<&2, String>>:
  Groups.members.of(List.take(&2, Types.Entry, r, 1n+m), s, g)

# whether g is a group of the store s at the version m of r (none: the groups
# are not good)
def Groups.is_group(
  r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String,
  m: Nat
) -> Maybe<&2, Bool>:
  Groups.is_group.of(List.take(&2, Types.Entry, r, 1n+m), s, g)

# the nodes of the group g of the store s at the version m of r, each once:
# its members that are no groups, and the nodes of its members that are groups
# (none: g is no group, or the groups are not good)
def Groups.nodes(
  r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  m: Nat
) -> Maybe<&2, List<&2, String>>:
  Groups.nodes.of(List.take(&2, Types.Entry, r, 1n+m), s, g)

# the owner group of the line c at the version m of r: that of the latest Own
# of c (none: there is none)
def Groups.owner(r: List<&2, Types.Entry>, c: Ledgers.Line, m: Nat) -> Maybe<&2, String>:
  Groups.own(List.take(&2, Types.Entry, r, 1n+m), c)

# Groups.good reads only the first 1n+m versions
def Groups.good_take(
  -r: List<&2, Types.Entry>,
  -r2: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -m: Nat,
  h: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(&2, Types.Entry, r2, 1n+m): List<&2, Types.Entry>
  }
) -> {Groups.good(r, s, m) == Groups.good(r2, s, m): Bool}:
  Equal.cong(
    List<&2, Types.Entry>,
    Bool,
    es => Groups.sound(es, s),
    List.take(&2, Types.Entry, r, 1n+m),
    List.take(&2, Types.Entry, r2, 1n+m),
    h
  )

# Groups.members reads only the first 1n+m versions
def Groups.members_take(
  -r: List<&2, Types.Entry>,
  -r2: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -m: Nat,
  h: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(&2, Types.Entry, r2, 1n+m): List<&2, Types.Entry>
  }
) -> {Groups.members(r, s, g, m) == Groups.members(r2, s, g, m): Maybe<&2, List<&2, String>>}:
  Equal.cong(
    List<&2, Types.Entry>,
    Maybe<&2, List<&2, String>>,
    es => Groups.members.of(es, s, g),
    List.take(&2, Types.Entry, r, 1n+m),
    List.take(&2, Types.Entry, r2, 1n+m),
    h
  )

# Groups.is_group reads only the first 1n+m versions
def Groups.is_group_take(
  -r: List<&2, Types.Entry>,
  -r2: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -m: Nat,
  h: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(&2, Types.Entry, r2, 1n+m): List<&2, Types.Entry>
  }
) -> {Groups.is_group(r, s, g, m) == Groups.is_group(r2, s, g, m): Maybe<&2, Bool>}:
  Equal.cong(
    List<&2, Types.Entry>,
    Maybe<&2, Bool>,
    es => Groups.is_group.of(es, s, g),
    List.take(&2, Types.Entry, r, 1n+m),
    List.take(&2, Types.Entry, r2, 1n+m),
    h
  )

# Groups.nodes reads only the first 1n+m versions
def Groups.nodes_take(
  -r: List<&2, Types.Entry>,
  -r2: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -m: Nat,
  h: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(&2, Types.Entry, r2, 1n+m): List<&2, Types.Entry>
  }
) -> {Groups.nodes(r, s, g, m) == Groups.nodes(r2, s, g, m): Maybe<&2, List<&2, String>>}:
  Equal.cong(
    List<&2, Types.Entry>,
    Maybe<&2, List<&2, String>>,
    es => Groups.nodes.of(es, s, g),
    List.take(&2, Types.Entry, r, 1n+m),
    List.take(&2, Types.Entry, r2, 1n+m),
    h
  )

# Groups.owner reads only the first 1n+m versions
def Groups.owner_take(
  -r: List<&2, Types.Entry>,
  -r2: List<&2, Types.Entry>,
  -c: Ledgers.Line,
  -m: Nat,
  h: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(&2, Types.Entry, r2, 1n+m): List<&2, Types.Entry>
  }
) -> {Groups.owner(r, c, m) == Groups.owner(r2, c, m): Maybe<&2, String>}:
  Equal.cong(
    List<&2, Types.Entry>,
    Maybe<&2, String>,
    es => Groups.own(es, c),
    List.take(&2, Types.Entry, r, 1n+m),
    List.take(&2, Types.Entry, r2, 1n+m),
    h
  )

# a gated answer is given only when the groups are good, and is the answer
def Groups.gate_some(
  -A: Data,
  b: Bool,
  -m: Maybe<&2, A>,
  -x: A
) -> {
  Groups.gate(A, b, m) == Some{x}: Maybe<&2, A>
} -> {b == True{}: Bool}
  & {m == Some{x}: Maybe<&2, A>}:
  match b:
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool} & {m == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case True{}:
      h => ({==}, h)

# a Maybe that is some has a value
def Maybe.is_some_true(
  -A: Data,
  m: Maybe<&2, A>
) -> {Maybe.is_some(&2, A, m) == True{}: Bool} -> Exists(A, x => {m == Some{x}: Maybe<&2, A>}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(A, x => {None{} == Some{x}: Maybe<&2, A>}),
        Shared.Bool.false_ne_true(h)
      )
    case Some{x}:
      h => (x, {==})

# a Maybe that is not some is none
def Maybe.is_some_false(
  -A: Data,
  m: Maybe<&2, A>
) -> {Maybe.is_some(&2, A, m) == False{}: Bool} -> {m == None{}: Maybe<&2, A>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Shared.Bool.true_ne_false(h))

# The laws of the latest version
# ------------------------------

# Groups.members_latest, from the latest Group of g in the first 1n+m versions
def Groups.members_latest.of(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  -ms: List<&2, String>,
  l: Groups.Last(
    List.take(&2, Types.Entry, r, 1n+m),
    Seek.Group{s, g},
    Spec.Request.Group{s, g, ms}
  )
) -> Exists(
  Nat,
  j => (
    Groups.At(r, j, Spec.Request.Group{s, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
  )
    & (
      @j2: Nat -> @ms2: List<
        &2,
        String> -> Groups.At(
        r,
        j2,
        Spec.Request.Group{s, g, ms2}
      ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+j, body) = l
  (hit, later) = body
  (at, fit) = hit
  (
    j,
    (
      Groups.At.of_take(r, j, m, Spec.Request.Group{s, g, ms}, at),
      +j2 => +ms2 => a2 => l2 => later(
        j2
      )(
        Spec.Request.Group{s, g, ms2}
      )(Groups.At.to_take(r, j2, m, Spec.Request.Group{s, g, ms2}, a2, l2))(Seek.group_refl(s, g))
    )
  )

# the members of a group are those of the latest Group of its name up to m
def Groups.members_latest(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ms: List<&2, String>,
  h: {Groups.members(r, s, g, m) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> Exists(
  Nat,
  j => (
    Groups.At(r, j, Spec.Request.Group{s, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
  )
    & (
      @j2: Nat -> @ms2: List<
        &2,
        String> -> Groups.At(
        r,
        j2,
        Spec.Request.Group{s, g, ms2}
      ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  Groups.members_latest.of(
    r,
    s,
    g,
    m,
    ms,
    Groups.mem_last(
      List.take(&2, Types.Entry, r, 1n+m),
      s,
      g,
      ms,
      Pair.snd(
        {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
        {
          Groups.mem(
            List.take(&2, Types.Entry, r, 1n+m),
            s,
            g
          )
            == Some{ms}: Maybe<&2, List<&2, String>>
        },
        Groups.gate_some(
          List<&2, String>,
          Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
          Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
          ms
        )(h)
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# Groups.is_group_yes, from the latest Group of g in the first 1n+m versions
def Groups.is_group_yes.of(
  +r: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  +m: Nat,
  ms: List<&2, String>,
  l: Groups.Last(
    List.take(&2, Types.Entry, r, 1n+m),
    Seek.Group{s, g},
    Spec.Request.Group{s, g, ms}
  )
) -> Exists(
  Nat,
  j => Exists(
    List<&2, String>,
    ms2 => Groups.At(r, j, Spec.Request.Group{s, g, ms2}) & {Nat.is_le(j, m) == True{}: Bool}
  )
):
  (+j, body) = l
  (hit, later) = body
  (at, fit) = hit
  (j, (ms, Groups.At.of_take(r, j, m, Spec.Request.Group{s, g, ms}, at)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a name that is a group has a Group version up to m
def Groups.is_group_yes(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  h: {Groups.is_group(r, s, g, m) == Some{True{}}: Maybe<&2, Bool>}
) -> Exists(
  Nat,
  j => Exists(
    List<&2, String>,
    ms => Groups.At(r, j, Spec.Request.Group{s, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
  )
):
  Exists.use(
    List<&2, String>,
    ms => {
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g) == Some{ms}: Maybe<&2, List<&2, String>>
    },
    Exists(
      Nat,
      j => Exists(
        List<&2, String>,
        ms => Groups.At(r, j, Spec.Request.Group{s, g, ms}) & {Nat.is_le(j, m) == True{}: Bool}
      )
    ),
    Maybe.is_some_true(
      List<&2, String>,
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)
    )(
      Shared.Maybe.some_inj(
        Bool,
        Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)),
        True{},
        Pair.snd(
          {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
          {
            Some{
              Maybe.is_some(
                &2,
                List<&2, String>,
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)
              )
            }
              == Some{True{}}: Maybe<&2, Bool>
          },
          Groups.gate_some(
            Bool,
            Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
            Some{
              Maybe.is_some(
                &2,
                List<&2, String>,
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)
              )
            },
            True{}
          )(h)
        )
      )
    ),
    +ms => hm => Groups.is_group_yes.of(
      r,
      s,
      g,
      m,
      ms,
      Groups.mem_last(List.take(&2, Types.Entry, r, 1n+m), s, g, ms, hm)
    )
  )

# a name that is no group has no Group version up to m
def Groups.is_group_no(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  h: {Groups.is_group(r, s, g, m) == Some{False{}}: Maybe<&2, Bool>}
) -> @j:
  Nat -> @ms: List<
    &2,
    String> -> Groups.At(
    r,
    j,
    Spec.Request.Group{s, g, ms}
  ) -> {Nat.is_le(j, m) == True{}: Bool} -> Empty:
  +j => +ms => a => l => Exists.use(
    List<&2, String>,
    ms2 => {
      Groups.mem(
        List.take(&2, Types.Entry, r, 1n+m),
        s,
        g
      )
        == Some{ms2}: Maybe<&2, List<&2, String>>
    },
    Empty,
    Groups.mem_of_at(
      List.take(&2, Types.Entry, r, 1n+m),
      s,
      g,
      j,
      ms,
      Groups.At.to_take(r, j, m, Spec.Request.Group{s, g, ms}, a, l)
    ),
    ms2 => hm => Shared.Bool.true_ne_false(
      (%hm: {Maybe.is_some(&2, List<&2, String>, _) == False{}: Bool}
        Shared.Maybe.some_inj(Bool, Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)), False{}, Pair.snd({Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool}, {Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g))} == Some{False{}}: Maybe<&2, Bool>}, Groups.gate_some(Bool, Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s), Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g))}, False{})(h))))
    )
  )

# Groups.owner_latest, from the latest Own of c in the first 1n+m versions
def Groups.owner_latest.of(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -g: String,
  l: Groups.Last(List.take(&2, Types.Entry, r, 1n+m), Seek.Own{c}, Spec.Request.Own{c, g})
) -> Exists(
  Nat,
  j => (
    Groups.At(r, j, Spec.Request.Own{c, g}) & {Nat.is_le(j, m) == True{}: Bool}
  )
    & (
      @j2: Nat -> @g2: String -> Groups.At(
        r,
        j2,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  (+j, body) = l
  (hit, later) = body
  (at, fit) = hit
  (
    j,
    (
      Groups.At.of_take(r, j, m, Spec.Request.Own{c, g}, at),
      +j2 => +g2 => a2 => l2 => later(
        j2
      )(
        Spec.Request.Own{c, g2}
      )(Groups.At.to_take(r, j2, m, Spec.Request.Own{c, g2}, a2, l2))(Ledgers.Line.is_eq_refl(c))
    )
  )

# the owner group of a line is that of the latest Own of the line up to m
def Groups.owner_latest(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  +g: String,
  h: {Groups.owner(r, c, m) == Some{g}: Maybe<&2, String>}
) -> Exists(
  Nat,
  j => (
    Groups.At(r, j, Spec.Request.Own{c, g}) & {Nat.is_le(j, m) == True{}: Bool}
  )
    & (
      @j2: Nat -> @g2: String -> Groups.At(
        r,
        j2,
        Spec.Request.Own{c, g2}
      ) -> {Nat.is_le(j2, m) == True{}: Bool} -> {Nat.is_le(j2, j) == True{}: Bool}
    )
):
  Groups.owner_latest.of(r, c, m, g, Groups.own_last(List.take(&2, Types.Entry, r, 1n+m), c, g, h))

# The laws of the nodes
# ---------------------

# the nodes of a group, one round deeper, hold the nodes of its members
def Groups.reach_step(
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -ms: List<&2, String>,
  -f: Nat,
  -x: String,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h: {List.contains(~String, ~String.eq, Groups.walk(f, ms, es, s), x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, Groups.reach(1n+f, g, es, s), x) == True{}: Bool}:
  %Equal.sym(
    Maybe<&2, List<&2, String>>,
    Groups.mem(es, s, g),
    Some{ms},
    hm
  ): {List.contains(~String, ~String.eq, Groups.walk(f, Groups.list(_), es, s), x) == True{}: Bool}
  h

# the nodes of a group, one round deeper, hold only the nodes of its members
def Groups.reach_back(
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -ms: List<&2, String>,
  -f: Nat,
  -x: String,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h: {List.contains(~String, ~String.eq, Groups.reach(1n+f, g, es, s), x) == True{}: Bool}
) -> {List.contains(~String, ~String.eq, Groups.walk(f, ms, es, s), x) == True{}: Bool}:
  %hm: {
    List.contains(~String, ~String.eq, Groups.walk(f, Groups.list(_), es, s), x) == True{}: Bool
  }
  h

# what the nodes of a group that is the same hold, they hold one round deeper
def Groups.same_up(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +x: String,
  hs: {Groups.same(g, es, s) == True{}: Bool},
  h: {
    List.contains(~String, ~String.eq, Groups.reach(Groups.fuel(es), g, es, s), x) == True{}: Bool
  }
) -> {
  List.contains(~String, ~String.eq, Groups.reach(1n+Groups.fuel(es), g, es, s), x) == True{}: Bool
}:
  Names.within_contains(
    Groups.reach(Groups.fuel(es), g, es, s),
    Groups.reach(1n+Groups.fuel(es), g, es, s),
    x,
    Shared.List.all.if_hit(
      Shared.List.within(
        ~String,
        ~String.eq,
        Groups.reach(Groups.fuel(es), g, es, s),
        Groups.reach(1n+Groups.fuel(es), g, es, s)
      ),
      u => Shared.List.within(
        ~String,
        ~String.eq,
        Groups.reach(1n+Groups.fuel(es), g, es, s),
        Groups.reach(Groups.fuel(es), g, es, s)
      )
    )(hs),
    h
  )

# what the nodes of a group that is the same hold one round deeper, they hold
def Groups.same_down(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +x: String,
  hs: {Groups.same(g, es, s) == True{}: Bool},
  h: {
    List.contains(
      ~String,
      ~String.eq,
      Groups.reach(1n+Groups.fuel(es), g, es, s),
      x
    )
      == True{}: Bool
  }
) -> {
  List.contains(~String, ~String.eq, Groups.reach(Groups.fuel(es), g, es, s), x) == True{}: Bool
}:
  Names.within_contains(
    Groups.reach(1n+Groups.fuel(es), g, es, s),
    Groups.reach(Groups.fuel(es), g, es, s),
    x,
    Shared.List.all.if_rest(
      Shared.List.within(
        ~String,
        ~String.eq,
        Groups.reach(Groups.fuel(es), g, es, s),
        Groups.reach(1n+Groups.fuel(es), g, es, s)
      ),
      u => Shared.List.within(
        ~String,
        ~String.eq,
        Groups.reach(1n+Groups.fuel(es), g, es, s),
        Groups.reach(Groups.fuel(es), g, es, s)
      )
    )(hs),
    h
  )

# when the groups are good, the nodes of a group are the set of what it reaches
def Groups.nodes_some(
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -ms: List<&2, String>,
  hs: {Groups.sound(es, s) == True{}: Bool},
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {
  Groups.nodes.of(
    es,
    s,
    g
  )
    == Some{Groups.set(Groups.reach(Groups.fuel(es), g, es, s))}: Maybe<&2, List<&2, String>>
}:
  %Equal.sym(
    Bool,
    Groups.sound(es, s),
    True{},
    hs
  ): {
    Groups.gate(
      List<&2, String>,
      _,
      Groups.nodes.pick(Groups.mem(es, s, g), Groups.set(Groups.reach(Groups.fuel(es), g, es, s)))
    )
      == Some{Groups.set(Groups.reach(Groups.fuel(es), g, es, s))}: Maybe<&2, List<&2, String>>
  }
  %Equal.sym(
    Maybe<&2, List<&2, String>>,
    Groups.mem(es, s, g),
    Some{ms},
    hm
  ): {
    Groups.nodes.pick(
      _,
      Groups.set(Groups.reach(Groups.fuel(es), g, es, s))
    )
      == Some{Groups.set(Groups.reach(Groups.fuel(es), g, es, s))}: Maybe<&2, List<&2, String>>
  }
  {==}

# when the groups are good, the members of a group are those that were found
def Groups.members_some(
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -g: String,
  -ms: List<&2, String>,
  hs: {Groups.sound(es, s) == True{}: Bool},
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {Groups.members.of(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}:
  %Equal.sym(
    Bool,
    Groups.sound(es, s),
    True{},
    hs
  ): {
    Groups.gate(List<&2, String>, _, Groups.mem(es, s, g)) == Some{ms}: Maybe<&2, List<&2, String>>
  }
  hm

# when the groups are good, a name is a group exactly when members were found
def Groups.is_group_some(
  -es: List<&2, Types.Entry>,
  -s: Hashes.Hash,
  -v: String,
  -mv: Maybe<&2, List<&2, String>>,
  hs: {Groups.sound(es, s) == True{}: Bool},
  hm: {Groups.mem(es, s, v) == mv: Maybe<&2, List<&2, String>>}
) -> {
  Groups.is_group.of(es, s, v) == Some{Maybe.is_some(&2, List<&2, String>, mv)}: Maybe<&2, Bool>
}:
  %Equal.sym(
    Bool,
    Groups.sound(es, s),
    True{},
    hs
  ): {
    Groups.gate(
      Bool,
      _,
      Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, v))}
    )
      == Some{Maybe.is_some(&2, List<&2, String>, mv)}: Maybe<&2, Bool>
  }
  %Equal.sym(
    Maybe<&2, List<&2, String>>,
    Groups.mem(es, s, v),
    mv,
    hm
  ): {
    Some{
      Maybe.is_some(&2, List<&2, String>, _)
    }
      == Some{Maybe.is_some(&2, List<&2, String>, mv)}: Maybe<&2, Bool>
  }
  {==}

# picked nodes are the nodes, and the name is a group
def Groups.nodes.pick_some(
  mv: Maybe<&2, List<&2, String>>,
  -ns: List<&2, String>,
  -vs: List<&2, String>
) -> {
  Groups.nodes.pick(mv, ns) == Some{vs}: Maybe<&2, List<&2, String>>
} -> {
  ns == vs: List<&2, String>
}
  & Exists(List<&2, String>, ms => {mv == Some{ms}: Maybe<&2, List<&2, String>>}):
  match mv:
    case None{}:
      h => Empty.absurd(
        {
          ns == vs: List<&2, String>
        }
          & Exists(List<&2, String>, ms => {None{} == Some{ms}: Maybe<&2, List<&2, String>>}),
        Shared.Maybe.none_ne_some(List<&2, String>, vs, h)
      )
    case Some{ms}:
      h => (Shared.Maybe.some_inj(List<&2, String>, ns, vs, h), (ms, {==}))

# a name of the nodes of a group is one that the group reaches
def Groups.nodes_in(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +v: String,
  +vs: List<&2, String>,
  +x: String,
  h4: {Groups.nodes.of(es, s, v) == Some{vs}: Maybe<&2, List<&2, String>>},
  h5: {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
) -> {
  List.contains(~String, ~String.eq, Groups.reach(Groups.fuel(es), v, es, s), x) == True{}: Bool
}:
  Groups.set_only(
    Groups.reach(Groups.fuel(es), v, es, s),
    x,
    (%Equal.sym(
      List<&2, String>,
      Groups.set(Groups.reach(Groups.fuel(es), v, es, s)),
      vs,
      Pair.fst(
        {Groups.set(Groups.reach(Groups.fuel(es), v, es, s)) == vs: List<&2, String>},
        Exists(
          List<&2, String>,
          ms => {Groups.mem(es, s, v) == Some{ms}: Maybe<&2, List<&2, String>>}
        ),
        Groups.nodes.pick_some(
          Groups.mem(es, s, v),
          Groups.set(Groups.reach(Groups.fuel(es), v, es, s)),
          vs
        )(
          Pair.snd(
            {Groups.sound(es, s) == True{}: Bool},
            {
              Groups.nodes.pick(
                Groups.mem(es, s, v),
                Groups.set(Groups.reach(Groups.fuel(es), v, es, s))
              )
                == Some{vs}: Maybe<&2, List<&2, String>>
            },
            Groups.gate_some(
              List<&2, String>,
              Groups.sound(es, s),
              Groups.nodes.pick(
                Groups.mem(es, s, v),
                Groups.set(Groups.reach(Groups.fuel(es), v, es, s))
              ),
              vs
            )(h4)
          )
        )
      )
    ): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
      h5)
  )

# a group that has nodes has members
def Groups.nodes_mem(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +v: String,
  +vs: List<&2, String>,
  h4: {Groups.nodes.of(es, s, v) == Some{vs}: Maybe<&2, List<&2, String>>}
) -> Exists(
  List<&2, String>,
  ms => {Groups.mem(es, s, v) == Some{ms}: Maybe<&2, List<&2, String>>}
):
  Pair.snd(
    {Groups.set(Groups.reach(Groups.fuel(es), v, es, s)) == vs: List<&2, String>},
    Exists(List<&2, String>, ms => {Groups.mem(es, s, v) == Some{ms}: Maybe<&2, List<&2, String>>}),
    Groups.nodes.pick_some(
      Groups.mem(es, s, v),
      Groups.set(Groups.reach(Groups.fuel(es), v, es, s)),
      vs
    )(
      Pair.snd(
        {Groups.sound(es, s) == True{}: Bool},
        {
          Groups.nodes.pick(
            Groups.mem(es, s, v),
            Groups.set(Groups.reach(Groups.fuel(es), v, es, s))
          )
            == Some{vs}: Maybe<&2, List<&2, String>>
        },
        Groups.gate_some(
          List<&2, String>,
          Groups.sound(es, s),
          Groups.nodes.pick(
            Groups.mem(es, s, v),
            Groups.set(Groups.reach(Groups.fuel(es), v, es, s))
          ),
          vs
        )(h4)
      )
    )
  )

# Groups.nodes_member, from the members that were found
def Groups.nodes_member.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  hs: {Groups.sound(es, s) == True{}: Bool},
  +hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  hv: {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>}
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
):
  (
    Groups.set(Groups.reach(Groups.fuel(es), g, es, s)),
    (
      Groups.nodes_some(es, s, g, ms, hs, hm),
      Groups.set_keeps(
        Groups.reach(Groups.fuel(es), g, es, s),
        v,
        Groups.reach_step(
          es,
          s,
          g,
          ms,
          1n+List.length(&2, Types.Entry, es),
          v,
          hm,
          Groups.walk_part(
            ms,
            1n+List.length(&2, Types.Entry, es),
            v,
            v,
            es,
            s,
            h2,
            (%Equal.sym(
              Maybe<&2, List<&2, String>>,
              Groups.mem(es, s, v),
              None{},
              hv
            ): {
              List.contains(
                ~String,
                ~String.eq,
                Groups.part(_, v, Groups.reach(1n+List.length(&2, Types.Entry, es), v, es, s)),
                v
              )
                == True{}: Bool
            }
              Names.contains_first(v, []))
          )
        )
      )
    )
  )

# Groups.nodes_nested, from the members that were found
def Groups.nodes_nested.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  +x: String,
  -vm: List<&2, String>,
  +hs: {Groups.sound(es, s) == True{}: Bool},
  +hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  hvm: {Groups.mem(es, s, v) == Some{vm}: Maybe<&2, List<&2, String>>},
  hx: {
    List.contains(~String, ~String.eq, Groups.reach(Groups.fuel(es), v, es, s), x) == True{}: Bool
  }
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  (
    Groups.set(Groups.reach(Groups.fuel(es), g, es, s)),
    (
      Groups.nodes_some(es, s, g, ms, hs, hm),
      Groups.set_keeps(
        Groups.reach(Groups.fuel(es), g, es, s),
        x,
        Groups.same_down(
          es,
          s,
          g,
          x,
          Groups.sound_same(es, s, g, ms, hs, hm),
          Groups.reach_step(
            es,
            s,
            g,
            ms,
            Groups.fuel(es),
            x,
            hm,
            Groups.walk_part(
              ms,
              Groups.fuel(es),
              v,
              x,
              es,
              s,
              h2,
              (%Equal.sym(
                Maybe<&2, List<&2, String>>,
                Groups.mem(es, s, v),
                Some{vm},
                hvm
              ): {
                List.contains(
                  ~String,
                  ~String.eq,
                  Groups.part(_, v, Groups.reach(Groups.fuel(es), v, es, s)),
                  x
                )
                  == True{}: Bool
              }
                hx)
            )
          )
        )
      )
    )
  )

# Groups.nodes_only.core for the member v, by its members (mv)
def Groups.nodes_only.at(
  mv: Maybe<&2, List<&2, String>>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +v: String,
  +x: String,
  +eqm: {Groups.mem(es, s, v) == mv: Maybe<&2, List<&2, String>>},
  +hs: {Groups.sound(es, s) == True{}: Bool},
  b2: {
    List.contains(
      ~String,
      ~String.eq,
      Groups.part(mv, v, Groups.reach(Groups.fuel(es), v, es, s)),
      x
    )
      == True{}: Bool
  }
) -> (
  {
    String.eq(v, x) == True{}: Bool
  }
    & {Groups.is_group.of(es, s, v) == Some{False{}}: Maybe<&2, Bool>}
)
  | (
    {
      Groups.is_group.of(es, s, v) == Some{True{}}: Maybe<&2, Bool>
    }
      & Exists(
        List<&2, String>,
        vs => {
          Groups.nodes.of(es, s, v) == Some{vs}: Maybe<&2, List<&2, String>>
        }
          & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
      )
  ):
  match mv:
    case None{}:
      Inl{(List.any.if_one(String.eq(v, x))(b2), Groups.is_group_some(es, s, v, None{}, hs, eqm))}
    case Some{vm}:
      Inr{
        (
          Groups.is_group_some(es, s, v, Some{vm}, hs, eqm),
          (
            Groups.set(Groups.reach(Groups.fuel(es), v, es, s)),
            (
              Groups.nodes_some(es, s, v, vm, hs, eqm),
              Groups.set_keeps(Groups.reach(Groups.fuel(es), v, es, s), x, b2)
            )
          )
        )
      }

# Groups.nodes_only, from the members that were found
def Groups.nodes_only.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +x: String,
  +hs: {Groups.sound(es, s) == True{}: Bool},
  +hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  hx: {
    List.contains(~String, ~String.eq, Groups.reach(Groups.fuel(es), g, es, s), x) == True{}: Bool
  }
) -> Exists(
  String,
  v => {
    List.contains(~String, ~String.eq, ms, v) == True{}: Bool
  }
    & (
      (
        {
          String.eq(v, x) == True{}: Bool
        }
          & {Groups.is_group.of(es, s, v) == Some{False{}}: Maybe<&2, Bool>}
      )
        | (
          {
            Groups.is_group.of(es, s, v) == Some{True{}}: Maybe<&2, Bool>
          }
            & Exists(
              List<&2, String>,
              vs => {
                Groups.nodes.of(es, s, v) == Some{vs}: Maybe<&2, List<&2, String>>
              }
                & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
            )
        )
    )
):
  Exists.use(
    String,
    v => {
      List.contains(~String, ~String.eq, ms, v) == True{}: Bool
    }
      & {
        List.contains(
          ~String,
          ~String.eq,
          Groups.part(Groups.mem(es, s, v), v, Groups.reach(Groups.fuel(es), v, es, s)),
          x
        )
          == True{}: Bool
      },
    Exists(
      String,
      v => {
        List.contains(~String, ~String.eq, ms, v) == True{}: Bool
      }
        & (
          (
            {
              String.eq(v, x) == True{}: Bool
            }
              & {Groups.is_group.of(es, s, v) == Some{False{}}: Maybe<&2, Bool>}
          )
            | (
              {
                Groups.is_group.of(es, s, v) == Some{True{}}: Maybe<&2, Bool>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Groups.nodes.of(es, s, v) == Some{vs}: Maybe<&2, List<&2, String>>
                  }
                    & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                )
            )
        )
    ),
    Groups.walk_only(
      ms,
      Groups.fuel(es),
      x,
      es,
      s,
      Groups.reach_back(
        es,
        s,
        g,
        ms,
        Groups.fuel(es),
        x,
        hm,
        Groups.same_up(es, s, g, x, Groups.sound_same(es, s, g, ms, hs, hm), hx)
      )
    ),
    +v => body => Pair.use(
      {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
      {
        List.contains(
          ~String,
          ~String.eq,
          Groups.part(Groups.mem(es, s, v), v, Groups.reach(Groups.fuel(es), v, es, s)),
          x
        )
          == True{}: Bool
      },
      Exists(
        String,
        v2 => {
          List.contains(~String, ~String.eq, ms, v2) == True{}: Bool
        }
          & (
            (
              {
                String.eq(v2, x) == True{}: Bool
              }
                & {Groups.is_group.of(es, s, v2) == Some{False{}}: Maybe<&2, Bool>}
            )
              | (
                {
                  Groups.is_group.of(es, s, v2) == Some{True{}}: Maybe<&2, Bool>
                }
                  & Exists(
                    List<&2, String>,
                    vs => {
                      Groups.nodes.of(es, s, v2) == Some{vs}: Maybe<&2, List<&2, String>>
                    }
                      & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                  )
              )
          )
      ),
      body,
      b1 => b2 => (v, (b1, Groups.nodes_only.at(Groups.mem(es, s, v), es, s, v, x, {==}, hs, b2)))
    )
  )

# whether members were found for a name is what Groups.is_group.of answers
def Groups.is_group_mem(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +v: String,
  +b: Bool,
  h: {Groups.is_group.of(es, s, v) == Some{b}: Maybe<&2, Bool>}
) -> {Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, v)) == b: Bool}:
  Shared.Maybe.some_inj(
    Bool,
    Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, v)),
    b,
    Pair.snd(
      {Groups.sound(es, s) == True{}: Bool},
      {Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, v))} == Some{b}: Maybe<&2, Bool>},
      Groups.gate_some(
        Bool,
        Groups.sound(es, s),
        Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, v))},
        b
      )(h)
    )
  )

# a member of a group that is no group is one of its nodes
def Groups.nodes_member(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ms: List<&2, String>,
  +v: String,
  h1: {Groups.members(r, s, g, m) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  h3: {Groups.is_group(r, s, v, m) == Some{False{}}: Maybe<&2, Bool>}
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
):
  Pair.use(
    {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
    {
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g) == Some{ms}: Maybe<&2, List<&2, String>>
    },
    Exists(
      List<&2, String>,
      ns => {
        Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
      }
        & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
    ),
    Groups.gate_some(
      List<&2, String>,
      Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
      ms
    )(h1),
    hs => hm => Groups.nodes_member.core(
      List.take(&2, Types.Entry, r, 1n+m),
      s,
      g,
      ms,
      v,
      hs,
      hm,
      h2,
      Maybe.is_some_false(
        List<&2, String>,
        Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v)
      )(Groups.is_group_mem(List.take(&2, Types.Entry, r, 1n+m), s, v, False{}, h3))
    )
  )

# a node of a member of a group that is a group is one of its nodes
def Groups.nodes_nested(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ms: List<&2, String>,
  +v: String,
  +x: String,
  +vs: List<&2, String>,
  h1: {Groups.members(r, s, g, m) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  h3: {Groups.is_group(r, s, v, m) == Some{True{}}: Maybe<&2, Bool>},
  +h4: {Groups.nodes(r, s, v, m) == Some{vs}: Maybe<&2, List<&2, String>>},
  h5: {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  Pair.use(
    {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
    {
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g) == Some{ms}: Maybe<&2, List<&2, String>>
    },
    Exists(
      List<&2, String>,
      ns => {
        Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    ),
    Groups.gate_some(
      List<&2, String>,
      Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
      ms
    )(h1),
    hs => hm => Exists.use(
      List<&2, String>,
      vm => {
        Groups.mem(
          List.take(&2, Types.Entry, r, 1n+m),
          s,
          v
        )
          == Some{vm}: Maybe<&2, List<&2, String>>
      },
      Exists(
        List<&2, String>,
        ns => {
          Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
        }
          & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
      ),
      Groups.nodes_mem(List.take(&2, Types.Entry, r, 1n+m), s, v, vs, h4),
      vm => hvm => Groups.nodes_nested.core(
        List.take(&2, Types.Entry, r, 1n+m),
        s,
        g,
        ms,
        v,
        x,
        vm,
        hs,
        hm,
        h2,
        hvm,
        Groups.nodes_in(List.take(&2, Types.Entry, r, 1n+m), s, v, vs, x, h4, h5)
      )
    )
  )

# a node of a group is a member that is no group, or a node of a member that
# is a group
def Groups.nodes_only(
  +r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +m: Nat,
  +ns: List<&2, String>,
  +x: String,
  +h1: {Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
) -> Exists(
  List<&2, String>,
  ms => {
    Groups.members(r, s, g, m) == Some{ms}: Maybe<&2, List<&2, String>>
  }
    & Exists(
      String,
      v => {
        List.contains(~String, ~String.eq, ms, v) == True{}: Bool
      }
        & (
          (
            {
              String.eq(v, x) == True{}: Bool
            }
              & {Groups.is_group(r, s, v, m) == Some{False{}}: Maybe<&2, Bool>}
          )
            | (
              {
                Groups.is_group(r, s, v, m) == Some{True{}}: Maybe<&2, Bool>
              }
                & Exists(
                  List<&2, String>,
                  vs => {
                    Groups.nodes(r, s, v, m) == Some{vs}: Maybe<&2, List<&2, String>>
                  }
                    & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                )
            )
        )
    )
):
  Exists.use(
    List<&2, String>,
    ms => {
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g) == Some{ms}: Maybe<&2, List<&2, String>>
    },
    Exists(
      List<&2, String>,
      ms => {
        Groups.members(r, s, g, m) == Some{ms}: Maybe<&2, List<&2, String>>
      }
        & Exists(
          String,
          v => {
            List.contains(~String, ~String.eq, ms, v) == True{}: Bool
          }
            & (
              (
                {
                  String.eq(v, x) == True{}: Bool
                }
                  & {Groups.is_group(r, s, v, m) == Some{False{}}: Maybe<&2, Bool>}
              )
                | (
                  {
                    Groups.is_group(r, s, v, m) == Some{True{}}: Maybe<&2, Bool>
                  }
                    & Exists(
                      List<&2, String>,
                      vs => {
                        Groups.nodes(r, s, v, m) == Some{vs}: Maybe<&2, List<&2, String>>
                      }
                        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                    )
                )
            )
        )
    ),
    Groups.nodes_mem(List.take(&2, Types.Entry, r, 1n+m), s, g, ns, h1),
    +ms => +hm => (
      ms,
      (
        Groups.members_some(
          List.take(&2, Types.Entry, r, 1n+m),
          s,
          g,
          ms,
          Pair.fst(
            {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
            {
              Groups.nodes.pick(
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
                Groups.set(
                  Groups.reach(
                    Groups.fuel(List.take(&2, Types.Entry, r, 1n+m)),
                    g,
                    List.take(&2, Types.Entry, r, 1n+m),
                    s
                  )
                )
              )
                == Some{ns}: Maybe<&2, List<&2, String>>
            },
            Groups.gate_some(
              List<&2, String>,
              Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
              Groups.nodes.pick(
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
                Groups.set(
                  Groups.reach(
                    Groups.fuel(List.take(&2, Types.Entry, r, 1n+m)),
                    g,
                    List.take(&2, Types.Entry, r, 1n+m),
                    s
                  )
                )
              ),
              ns
            )(h1)
          ),
          hm
        ),
        Groups.nodes_only.core(
          List.take(&2, Types.Entry, r, 1n+m),
          s,
          g,
          ms,
          x,
          Pair.fst(
            {Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s) == True{}: Bool},
            {
              Groups.nodes.pick(
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
                Groups.set(
                  Groups.reach(
                    Groups.fuel(List.take(&2, Types.Entry, r, 1n+m)),
                    g,
                    List.take(&2, Types.Entry, r, 1n+m),
                    s
                  )
                )
              )
                == Some{ns}: Maybe<&2, List<&2, String>>
            },
            Groups.gate_some(
              List<&2, String>,
              Groups.sound(List.take(&2, Types.Entry, r, 1n+m), s),
              Groups.nodes.pick(
                Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g),
                Groups.set(
                  Groups.reach(
                    Groups.fuel(List.take(&2, Types.Entry, r, 1n+m)),
                    g,
                    List.take(&2, Types.Entry, r, 1n+m),
                    s
                  )
                )
              ),
              ns
            )(h1)
          ),
          hm,
          Groups.nodes_in(List.take(&2, Types.Entry, r, 1n+m), s, g, ns, x, h1, h2)
        )
      )
    )
  )
