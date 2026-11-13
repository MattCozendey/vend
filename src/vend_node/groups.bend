import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/reach.bend as Reaches
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

# Closures
# --------
# The nodes that a level reaches in a graph (reach.bend): a search by levels
# that keeps the nodes it saw, so that it visits each node once.

# x <> rest, when neither seen nor rest holds x, else rest
def Closure.fresh.put(
  ~A: Data,
  ~same: A -> A -> Bool,
  +x: A,
  +rest: List<&2, A>,
  seen: List<&2, A>
) -> List<&2, A>:
  Shared.Bool.when(
    List<&2, A>,
    List.contains(~A, ~same, seen, x),
    u => rest,
    u => List.filter.put(A, x, rest, Bool.not(List.contains(~A, ~same, rest, x)))
  )

# the nodes of xs that seen lacks, each once
def Closure.fresh(
  ~A: Data,
  ~same: A -> A -> Bool,
  xs: List<&2, A>,
  +seen: List<&2, A>
) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Closure.fresh.put(~A, ~same, x, Closure.fresh(~A, ~same, r, seen), seen)

# the nodes ks, the level ws, and each node that a search f levels deep finds
# from ws, each once when ks and then ws holds each once
def Closure.go(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  f: Nat,
  ws: List<&2, A>,
  +g: V,
  ks: List<&2, A>
) -> List<&2, A>:
  match f ws:
    case 0n xs:
      List.append(&2, A, ks, xs)
    case 1n+e Nil{}:
      ks
    case 1n+e Con{+w, +r}:
      +seen = List.append(&2, A, ks, w <> r)
      Closure.go(
        ~A,
        ~V,
        ~same,
        ~succ,
        e,
        Closure.fresh(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, w <> r, g), seen),
        g,
        seen
      )

# the nodes of the level xs and each node that they reach in g, at any depth,
# each once
def Closure.of(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  +g: V,
  xs: List<&2, A>
) -> List<&2, A>:
  Closure.go(
    ~A,
    ~V,
    ~same,
    ~succ,
    List.length(&2, A, nodes(g)),
    Closure.fresh(~A, ~same, xs, []),
    g,
    []
  )

# The laws of closures
# --------------------

# a list that starts with x holds x
def Closure.contains_head(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +x: A,
  r: List<&2, A>
) -> {List.contains(~A, ~same, x <> r, x) == True{}: Bool}:
  %Equal.sym(
    Bool,
    same(x, x),
    True{},
    Shared.Eq.refl(~A, ~same, laws, x)
  ): {List.any.if(u => List.contains(~A, ~same, r, x), _) == True{}: Bool}
  {==}

# Closure.fresh_within at the first node x, by whether seen holds it (cs) and
# the fresh nodes of the rest hold it (cr)
def Closure.fresh_within.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +cs: Bool,
  +cr: Bool,
  +x: A,
  +r: List<&2, A>,
  +rest: List<&2, A>,
  ih: {Shared.List.within(~A, ~same, rest, r) == True{}: Bool}
) -> {
  Shared.List.within(
    ~A,
    ~same,
    Shared.Bool.when(List<&2, A>, cs, u => rest, u => List.filter.put(A, x, rest, Bool.not(cr))),
    x <> r
  )
    == True{}: Bool
}:
  match cs cr:
    case True{} True{}:
      Reaches.Reach.within_right(~A, ~same, rest, [x], r)(ih)
    case True{} False{}:
      Reaches.Reach.within_right(~A, ~same, rest, [x], r)(ih)
    case False{} True{}:
      Reaches.Reach.within_right(~A, ~same, rest, [x], r)(ih)
    case False{} False{}:
      Shared.Bool.and_both(
        List.contains(~A, ~same, x <> r, x),
        Shared.List.within(~A, ~same, rest, x <> r)
      )(
        Closure.contains_head(~A, ~same, ~laws, x, r)
      )(Reaches.Reach.within_right(~A, ~same, rest, [x], r)(ih))

# the fresh nodes of xs are nodes of xs
def Closure.fresh_within(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +seen: List<&2, A>
) -> {Shared.List.within(~A, ~same, Closure.fresh(~A, ~same, xs, seen), xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Closure.fresh_within.at(
        ~A,
        ~same,
        ~laws,
        List.contains(~A, ~same, seen, x),
        List.contains(~A, ~same, Closure.fresh(~A, ~same, r, seen), x),
        x,
        r,
        Closure.fresh(~A, ~same, r, seen),
        Closure.fresh_within(~A, ~same, ~laws, r, seen)
      )

# Closure.fresh_covers at the first node x, by whether seen holds it (cs) and
# the fresh nodes of the rest hold it (cr)
def Closure.fresh_covers.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +cs: Bool,
  +cr: Bool,
  +x: A,
  +r: List<&2, A>,
  +seen: List<&2, A>,
  +rest: List<&2, A>,
  ih: {Shared.List.within(~A, ~same, r, List.append(&2, A, seen, rest)) == True{}: Bool}
) -> {
  List.contains(~A, ~same, seen, x) == cs: Bool
} -> {
  List.contains(~A, ~same, rest, x) == cr: Bool
} -> {
  Bool.and(
    List.contains(
      ~A,
      ~same,
      List.append(
        &2,
        A,
        seen,
        Shared.Bool.when(List<&2, A>, cs, u => rest, u => List.filter.put(A, x, rest, Bool.not(cr)))
      ),
      x
    ),
    Shared.List.within(
      ~A,
      ~same,
      r,
      List.append(
        &2,
        A,
        seen,
        Shared.Bool.when(List<&2, A>, cs, u => rest, u => List.filter.put(A, x, rest, Bool.not(cr)))
      )
    )
  )
    == True{}: Bool
}:
  match cs cr:
    case True{} True{}:
      +hs => +hr => Shared.Bool.and_both(
        List.contains(~A, ~same, List.append(&2, A, seen, rest), x),
        Shared.List.within(~A, ~same, r, List.append(&2, A, seen, rest))
      )(Shared.List.contains_left(~A, ~same, seen, rest, x, hs))(ih)
    case True{} False{}:
      +hs => +hr => Shared.Bool.and_both(
        List.contains(~A, ~same, List.append(&2, A, seen, rest), x),
        Shared.List.within(~A, ~same, r, List.append(&2, A, seen, rest))
      )(Shared.List.contains_left(~A, ~same, seen, rest, x, hs))(ih)
    case False{} True{}:
      +hs => +hr => Shared.Bool.and_both(
        List.contains(~A, ~same, List.append(&2, A, seen, rest), x),
        Shared.List.within(~A, ~same, r, List.append(&2, A, seen, rest))
      )(Shared.List.contains_right(~A, ~same, seen, rest, x, hr))(ih)
    case False{} False{}:
      +hs => +hr => Shared.Bool.and_both(
        List.contains(~A, ~same, List.append(&2, A, seen, x <> rest), x),
        Shared.List.within(~A, ~same, r, List.append(&2, A, seen, x <> rest))
      )(
        Shared.List.contains_right(
          ~A,
          ~same,
          seen,
          x <> rest,
          x,
          Closure.contains_head(~A, ~same, ~laws, x, rest)
        )
      )(
        Reaches.Reach.within_trans(
          ~A,
          ~same,
          ~laws,
          r,
          List.append(&2, A, seen, rest),
          List.append(&2, A, seen, x <> rest)
        )(
          ih
        )(
          Reaches.Reach.within_both(
            ~A,
            ~same,
            seen,
            rest,
            List.append(&2, A, seen, x <> rest)
          )(
            Reaches.Reach.within_left(
              ~A,
              ~same,
              seen,
              seen,
              x <> rest
            )(Reaches.Reach.within_self(~A, ~same, ~laws, seen))
          )(
            Reaches.Reach.within_right(
              ~A,
              ~same,
              rest,
              seen,
              x <> rest
            )(
              Reaches.Reach.within_right(
                ~A,
                ~same,
                rest,
                [x],
                rest
              )(Reaches.Reach.within_self(~A, ~same, ~laws, rest))
            )
          )
        )
      )

# each node of xs is in seen or among the fresh nodes of xs
def Closure.fresh_covers(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +seen: List<&2, A>
) -> {
  Shared.List.within(
    ~A,
    ~same,
    xs,
    List.append(&2, A, seen, Closure.fresh(~A, ~same, xs, seen))
  )
    == True{}: Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Closure.fresh_covers.at(
        ~A,
        ~same,
        ~laws,
        List.contains(~A, ~same, seen, x),
        List.contains(~A, ~same, Closure.fresh(~A, ~same, r, seen), x),
        x,
        r,
        seen,
        Closure.fresh(~A, ~same, r, seen),
        Closure.fresh_covers(~A, ~same, ~laws, r, seen)
      )({==})({==})

# the search keeps the nodes that it starts with
def Closure.go_keeps(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +f: Nat,
  +ws: List<&2, A>,
  +g: V,
  +ks: List<&2, A>,
  +m: A
) -> {
  List.contains(~A, ~same, List.append(&2, A, ks, ws), m) == True{}: Bool
} -> {List.contains(~A, ~same, Closure.go(~A, ~V, ~same, ~succ, f, ws, g, ks), m) == True{}: Bool}:
  match f ws:
    case 0n xs:
      +h => h
    case 1n+e Nil{}:
      +h =>
        %Shared.List.append_nil(A, ks): {List.contains(~A, ~same, _, m) == True{}: Bool}
        h
    case 1n+e Con{+w, +r}:
      +h => Closure.go_keeps(
        ~A,
        ~V,
        ~same,
        ~succ,
        e,
        Closure.fresh(
          ~A,
          ~same,
          Reaches.Reach.next(~A, ~V, ~succ, w <> r, g),
          List.append(&2, A, ks, w <> r)
        ),
        g,
        List.append(&2, A, ks, w <> r),
        m
      )(
        Shared.List.contains_left(
          ~A,
          ~same,
          List.append(&2, A, ks, w <> r),
          Closure.fresh(
            ~A,
            ~same,
            Reaches.Reach.next(~A, ~V, ~succ, w <> r, g),
            List.append(&2, A, ks, w <> r)
          ),
          m,
          h
        )
      )

# a path from a level is a path from any level that holds its first node
def Closure.path_from(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ps: List<&2, A>,
  +ys: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {
  List.contains(~A, ~same, xs, Reaches.Reach.first(A, ps, m)) == True{}: Bool
} -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  match ps:
    case Nil{}:
      +h1 => +h2 => h2
    case Con{+p, +r}:
      +h1 => +h2 => Shared.Bool.and_both(
        List.contains(~A, ~same, xs, p),
        Reaches.Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
      )(
        h2
      )(
        Shared.Bool.and_true_right(
          List.contains(~A, ~same, ys, p),
          Reaches.Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
        )(h1)
      )

# a path from a level is a path from any level that holds its nodes
def Closure.path_wider(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +ys: List<&2, A>,
  +xs: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ys, g, m) == True{}: Bool
} -> {
  Shared.List.within(~A, ~same, ys, xs) == True{}: Bool
} -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  +h => +hw => Closure.path_from(
    ~A,
    ~V,
    ~same,
    ~succ,
    ps,
    ys,
    xs,
    g,
    m
  )(
    h
  )(
    Reaches.Reach.within_in(
      ~A,
      ~same,
      ~laws,
      ys,
      xs,
      Reaches.Reach.first(A, ps, m)
    )(hw)(Reaches.Reach.path_first(~A, ~V, ~same, ~succ, ps, ys, g, m)(h))
  )

# one side of a true "or" is true
def Closure.or_split(
  a: Bool,
  b: Bool
) -> {Bool.or(a, b) == True{}: Bool} -> {a == True{}: Bool}
  | {b == True{}: Bool}:
  match a:
    case True{}:
      h => Inl{{==}}
    case False{}:
      h => Inr{h}

# Closure.go_path.here, by which of ks and ws holds m
def Closure.go_path.pick(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ks: List<&2, A>,
  +ws: List<&2, A>,
  +g: V,
  +m: A,
  r: {
    List.contains(~A, ~same, ks, m) == True{}: Bool
  }
    | {List.contains(~A, ~same, ws, m) == True{}: Bool}
) -> {
  List.contains(~A, ~same, ks, m) == True{}: Bool
}
  | (&ps: List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ws, g, m) == True{}: Bool}):
  match r:
    case Inl{h}:
      Inl{h}
    case Inr{h}:
      Inr{([], h)}

# a node of ks and then ws is in ks, or the level ws finds it
def Closure.go_path.here(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ks: List<&2, A>,
  +ws: List<&2, A>,
  +g: V,
  +m: A
) -> {
  List.contains(~A, ~same, List.append(&2, A, ks, ws), m) == True{}: Bool
} -> {
  List.contains(~A, ~same, ks, m) == True{}: Bool
}
  | (&ps: List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ws, g, m) == True{}: Bool}):
  h => Closure.go_path.pick(
    ~A,
    ~V,
    ~same,
    ~succ,
    ks,
    ws,
    g,
    m,
    Closure.or_split(
      List.contains(~A, ~same, ks, m),
      List.contains(~A, ~same, ws, m)
    )(
      Equal.trans(
        Bool,
        Bool.or(List.contains(~A, ~same, ks, m), List.contains(~A, ~same, ws, m)),
        List.contains(~A, ~same, List.append(&2, A, ks, ws), m),
        True{},
        Equal.sym(
          Bool,
          List.contains(~A, ~same, List.append(&2, A, ks, ws), m),
          Bool.or(List.contains(~A, ~same, ks, m), List.contains(~A, ~same, ws, m)),
          Shared.List.contains_append(~A, ~same, ks, ws, m)
        ),
        h
      )
    )
  )

# Closure.go_path.lift, once the node y of ws before the path is found
def Closure.go_path.cons(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  +ws: List<&2, A>,
  +ps: List<&2, A>,
  +g: V,
  +m: A,
  w: &y: A -> {
    List.contains(~A, ~same, ws, y) == True{}: Bool
  }
    & {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m) == True{}: Bool}
) -> &qs:
  List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, qs, ws, g, m) == True{}: Bool}:
  match w:
    case (+y, (h1, h2)):
      (
        y <> ps,
        Shared.Bool.and_both(
          List.contains(~A, ~same, ws, y),
          Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, succ(g)(y), g, m)
        )(h1)(h2)
      )

# a path from the fresh nodes of the next level of ws gives a path from ws
def Closure.go_path.lift(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ws: List<&2, A>,
  +seen: List<&2, A>,
  +g: V,
  +m: A,
  v: &ps: List<
    &2,
    A> -> {
    Reaches.Reach.path(
      ~A,
      ~V,
      ~same,
      ~succ,
      ps,
      Closure.fresh(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, ws, g), seen),
      g,
      m
    )
      == True{}: Bool
  }
) -> &qs:
  List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, qs, ws, g, m) == True{}: Bool}:
  match v:
    case (+ps, hp):
      Closure.go_path.cons(
        ~A,
        ~V,
        ~same,
        ~succ,
        ws,
        ps,
        g,
        m,
        Reaches.Reach.path_step(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          ws,
          ps,
          g,
          m
        )(
          Closure.path_wider(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            ps,
            Closure.fresh(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, ws, g), seen),
            Reaches.Reach.next(~A, ~V, ~succ, ws, g),
            g,
            m
          )(
            hp
          )(Closure.fresh_within(~A, ~same, ~laws, Reaches.Reach.next(~A, ~V, ~succ, ws, g), seen))
        )
      )

# Closure.go_path one level down, from what the next levels give
def Closure.go_path.down(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ks: List<&2, A>,
  +ws: List<&2, A>,
  +g: V,
  +m: A,
  res: {
    List.contains(~A, ~same, List.append(&2, A, ks, ws), m) == True{}: Bool
  }
    | (
      &ps: List<
        &2,
        A> -> {
        Reaches.Reach.path(
          ~A,
          ~V,
          ~same,
          ~succ,
          ps,
          Closure.fresh(
            ~A,
            ~same,
            Reaches.Reach.next(~A, ~V, ~succ, ws, g),
            List.append(&2, A, ks, ws)
          ),
          g,
          m
        )
          == True{}: Bool
      }
    )
) -> {
  List.contains(~A, ~same, ks, m) == True{}: Bool
}
  | (&ps: List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ws, g, m) == True{}: Bool}):
  match res:
    case Inl{h}:
      Closure.go_path.here(~A, ~V, ~same, ~succ, ks, ws, g, m)(h)
    case Inr{v}:
      Inr{
        Closure.go_path.lift(~A, ~V, ~same, ~succ, ~laws, ws, List.append(&2, A, ks, ws), g, m, v)
      }

# a node that the search finds is one it started with (ks), or has a path from
# the level ws
def Closure.go_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +f: Nat,
  +ws: List<&2, A>,
  +g: V,
  +ks: List<&2, A>,
  +m: A
) -> {
  List.contains(~A, ~same, Closure.go(~A, ~V, ~same, ~succ, f, ws, g, ks), m) == True{}: Bool
} -> {
  List.contains(~A, ~same, ks, m) == True{}: Bool
}
  | (&ps: List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, ws, g, m) == True{}: Bool}):
  match f ws:
    case 0n xs:
      h => Closure.go_path.here(~A, ~V, ~same, ~succ, ks, xs, g, m)(h)
    case 1n+e Nil{}:
      h => Inl{h}
    case 1n+e Con{+w, +r}:
      h => Closure.go_path.down(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        ks,
        w <> r,
        g,
        m,
        Closure.go_path(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          e,
          Closure.fresh(
            ~A,
            ~same,
            Reaches.Reach.next(~A, ~V, ~succ, w <> r, g),
            List.append(&2, A, ks, w <> r)
          ),
          g,
          List.append(&2, A, ks, w <> r),
          m
        )(h)
      )

# what fits in f fits in one more
def Closure.fits_more(
  -A: Data,
  ps: List<&2, A>,
  f: Nat
) -> {
  Reaches.Reach.fits(A, ps, f) == True{}: Bool
} -> {Reaches.Reach.fits(A, ps, 1n+f) == True{}: Bool}:
  match ps f:
    case Nil{} n:
      h => {==}
    case Con{p, r} 0n:
      h => Empty.absurd(
        {Reaches.Reach.fits(A, p <> r, 1n) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{p, r} 1n+n:
      h => Closure.fits_more(A, r, n)(h)

# the next level of the nodes seen is within them and the fresh nodes of the
# next level of ws, when the next level of ks is within ks and then ws
def Closure.next_covers(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ks: List<&2, A>,
  +ws: List<&2, A>,
  +g: V
) -> {
  Shared.List.within(
    ~A,
    ~same,
    Reaches.Reach.next(~A, ~V, ~succ, ks, g),
    List.append(&2, A, ks, ws)
  )
    == True{}: Bool
} -> {
  Shared.List.within(
    ~A,
    ~same,
    Reaches.Reach.next(~A, ~V, ~succ, List.append(&2, A, ks, ws), g),
    List.append(
      &2,
      A,
      List.append(&2, A, ks, ws),
      Closure.fresh(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, ws, g), List.append(&2, A, ks, ws))
    )
  )
    == True{}: Bool
}:
  h =>
    +seen = List.append(&2, A, ks, ws)
    +next1 = Reaches.Reach.next(~A, ~V, ~succ, ws, g)
    +new = Closure.fresh(~A, ~same, next1, seen)
    Reaches.Reach.within_trans(
      ~A,
      ~same,
      ~laws,
      Reaches.Reach.next(~A, ~V, ~succ, seen, g),
      List.append(&2, A, seen, next1),
      List.append(&2, A, seen, new)
    )(
      Reaches.Reach.next_grown(~A, ~V, ~same, ~succ, ~laws, ks, ws, g)(h)
    )(
      Reaches.Reach.within_both(
        ~A,
        ~same,
        seen,
        next1,
        List.append(&2, A, seen, new)
      )(
        Reaches.Reach.within_left(
          ~A,
          ~same,
          seen,
          seen,
          new
        )(Reaches.Reach.within_self(~A, ~same, ~laws, seen))
      )(Closure.fresh_covers(~A, ~same, ~laws, next1, seen))
    )

# Closure.go_full after the first node p of the path, which is seen: the rest
# of the path is a path from any level js that holds the next level of seen
def Closure.go_full.step(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +seen: List<&2, A>,
  +js: List<&2, A>,
  +p: A,
  +r: List<&2, A>,
  +g: V,
  +m: A
) -> {
  Shared.List.within(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, seen, g), js) == True{}: Bool
} -> {
  Bool.and(
    List.contains(~A, ~same, seen, p),
    Reaches.Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
  )
    == True{}: Bool
} -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, r, js, g, m) == True{}: Bool}:
  hj => +hp =>
    +path1 = Reaches.Reach.path(~A, ~V, ~same, ~succ, r, succ(g)(p), g, m)
    +contains1 = List.contains(~A, ~same, seen, p)
    Closure.path_from(
      ~A,
      ~V,
      ~same,
      ~succ,
      r,
      succ(g)(p),
      js,
      g,
      m
    )(
      Shared.Bool.and_true_right(contains1, path1)(hp)
    )(
      Reaches.Reach.within_in(
        ~A,
        ~same,
        ~laws,
        Reaches.Reach.next(~A, ~V, ~succ, seen, g),
        js,
        Reaches.Reach.first(A, r, m)
      )(
        hj
      )(
        Reaches.Reach.found_sub(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          seen,
          p,
          Reaches.Reach.first(A, r, m),
          g
        )(
          Shared.Bool.and_true_left(contains1, path1)(hp)
        )(
          Reaches.Reach.path_first(
            ~A,
            ~V,
            ~same,
            ~succ,
            r,
            succ(g)(p),
            g,
            m
          )(Shared.Bool.and_true_right(contains1, path1)(hp))
        )
      )
    )

# the search finds the end of each path from the nodes seen (ks and then ws)
# that is no longer than the search is deep, when the next level of ks is
# within the nodes seen
def Closure.go_full(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +ps: List<&2, A>,
  +f: Nat,
  +ws: List<&2, A>,
  +g: V,
  +ks: List<&2, A>,
  +m: A
) -> {
  Shared.List.within(
    ~A,
    ~same,
    Reaches.Reach.next(~A, ~V, ~succ, ks, g),
    List.append(&2, A, ks, ws)
  )
    == True{}: Bool
} -> {
  Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, List.append(&2, A, ks, ws), g, m) == True{}: Bool
} -> {
  Reaches.Reach.fits(A, ps, f) == True{}: Bool
} -> {List.contains(~A, ~same, Closure.go(~A, ~V, ~same, ~succ, f, ws, g, ks), m) == True{}: Bool}:
  match ps f ws:
    case Nil{} 0n xs:
      hj => hp => hf => hp
    case Nil{} 1n+e Nil{}:
      hj => hp => hf =>
        %Shared.List.append_nil(A, ks): {List.contains(~A, ~same, _, m) == True{}: Bool}
        hp
    case Nil{} 1n+e Con{+w, +r}:
      hj => hp => hf => Closure.go_keeps(~A, ~V, ~same, ~succ, 1n+e, w <> r, g, ks, m)(hp)
    case Con{p, rp} 0n xs:
      hj => hp => hf => Empty.absurd(
        {List.contains(~A, ~same, List.append(&2, A, ks, xs), m) == True{}: Bool},
        Shared.Bool.false_ne_true(hf)
      )
    case Con{+p, +rp} 1n+e Nil{}:
      +hj => hp => hf => Closure.go_full(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        rp,
        1n+e,
        [],
        g,
        ks,
        m
      )(
        hj
      )(
        Closure.go_full.step(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          List.append(&2, A, ks, []),
          List.append(&2, A, ks, []),
          p,
          rp,
          g,
          m
        )(
          %Equal.sym(List<&2, A>, List.append(&2, A, ks, []), ks, Shared.List.append_nil(A, ks)): {Shared.List.within(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, _, g), List.append(&2, A, ks, [])) == True{}: Bool}
          hj)(hp)
      )(Closure.fits_more(A, rp, e)(hf))
    case Con{+p, +rp} 1n+e Con{+w, +r}:
      hj => hp => hf =>
        +seen = List.append(&2, A, ks, w <> r)
        +new = Closure.fresh(~A, ~same, Reaches.Reach.next(~A, ~V, ~succ, w <> r, g), seen)
        +hn = Closure.next_covers(~A, ~V, ~same, ~succ, ~laws, ks, w <> r, g)(hj)
        Closure.go_full(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          rp,
          e,
          new,
          g,
          seen,
          m
        )(
          hn
        )(
          Closure.go_full.step(
            ~A,
            ~V,
            ~same,
            ~succ,
            ~laws,
            seen,
            List.append(&2, A, seen, new),
            p,
            rp,
            g,
            m
          )(hn)(hp)
        )(hf)

# Closure.of_path, once the path from the fresh nodes of xs is found
def Closure.of_path.wide(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +g: V,
  +m: A,
  v: &ps: List<
    &2,
    A> -> {
    Reaches.Reach.path(
      ~A,
      ~V,
      ~same,
      ~succ,
      ps,
      Closure.fresh(~A, ~same, xs, []),
      g,
      m
    )
      == True{}: Bool
  }
) -> &ps:
  List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  match v:
    case (+ps, hp):
      (
        ps,
        Closure.path_wider(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          ps,
          Closure.fresh(~A, ~same, xs, []),
          xs,
          g,
          m
        )(hp)(Closure.fresh_within(~A, ~same, ~laws, xs, []))
      )

# Closure.of_path, from what the search gives
def Closure.of_path.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +g: V,
  +m: A,
  res: {
    List.contains(~A, ~same, [], m) == True{}: Bool
  }
    | (
      &ps: List<
        &2,
        A> -> {
        Reaches.Reach.path(
          ~A,
          ~V,
          ~same,
          ~succ,
          ps,
          Closure.fresh(~A, ~same, xs, []),
          g,
          m
        )
          == True{}: Bool
      }
    )
) -> &ps:
  List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  match res:
    case Inl{h}:
      Empty.absurd(
        &ps: List<
          &2,
          A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Inr{v}:
      Closure.of_path.wide(~A, ~V, ~same, ~succ, ~laws, xs, g, m, v)

# a node of the closure of the level xs has a path from xs
def Closure.of_path(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  +g: V,
  +xs: List<&2, A>,
  +m: A
) -> {
  List.contains(~A, ~same, Closure.of(~A, ~V, ~same, ~succ, ~nodes, g, xs), m) == True{}: Bool
} -> &ps:
  List<&2, A> -> {Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool}:
  h => Closure.of_path.at(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~laws,
    xs,
    g,
    m,
    Closure.go_path(
      ~A,
      ~V,
      ~same,
      ~succ,
      ~laws,
      List.length(&2, A, nodes(g)),
      Closure.fresh(~A, ~same, xs, []),
      g,
      [],
      m
    )(h)
  )

# Closure.path_of, once the path is cut to visit each node once
def Closure.path_of.cut(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
  +g: V,
  +xs: List<&2, A>,
  +m: A,
  w: &qs: List<
    &2,
    A> -> {
    Reaches.Reach.path(~A, ~V, ~same, ~succ, qs, xs, g, m) == True{}: Bool
  }
    & {Reaches.Reach.distinct(~A, ~same, qs) == True{}: Bool}
) -> {List.contains(~A, ~same, Closure.of(~A, ~V, ~same, ~succ, ~nodes, g, xs), m) == True{}: Bool}:
  match w:
    case (+qs, (+hq, hd)):
      Closure.go_full(
        ~A,
        ~V,
        ~same,
        ~succ,
        ~laws,
        qs,
        List.length(&2, A, nodes(g)),
        Closure.fresh(~A, ~same, xs, []),
        g,
        [],
        m
      )(
        {==}
      )(
        Closure.path_wider(
          ~A,
          ~V,
          ~same,
          ~succ,
          ~laws,
          qs,
          xs,
          Closure.fresh(~A, ~same, xs, []),
          g,
          m
        )(hq)(Closure.fresh_covers(~A, ~same, ~laws, xs, []))
      )(
        Reaches.Reach.fits_nodes(
          ~A,
          ~same,
          ~laws,
          qs,
          nodes(g)
        )(hd)(Reaches.Reach.path_within(~A, ~V, ~same, ~succ, ~nodes, ~live, qs, xs, g, m)(hq))
      )

# the end of a path from the level xs is in the closure of xs, in a graph
# whose nodes with successors are among nodes(g)
def Closure.path_of(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~succ: V -> A -> List<&2, A>,
  ~nodes: V -> List<&2, A>,
  ~laws: Shared.Eq.Laws(A, same),
  ~live: @g: V -> @p: A -> @q: A -> {
    List.contains(~A, ~same, succ(g)(p), q) == True{}: Bool
  } -> {List.contains(~A, ~same, nodes(g), p) == True{}: Bool},
  +g: V,
  +xs: List<&2, A>,
  +ps: List<&2, A>,
  +m: A
) -> {
  Reaches.Reach.path(~A, ~V, ~same, ~succ, ps, xs, g, m) == True{}: Bool
} -> {List.contains(~A, ~same, Closure.of(~A, ~V, ~same, ~succ, ~nodes, g, xs), m) == True{}: Bool}:
  h => Closure.path_of.cut(
    ~A,
    ~V,
    ~same,
    ~succ,
    ~nodes,
    ~laws,
    ~live,
    g,
    xs,
    m,
    Reaches.Reach.shorten(~A, ~V, ~same, ~succ, ~laws, ps, xs, g, m)(h)
  )

# The reads
# ---------
# The groups of a store are a graph: a name leads to its members. The nodes of
# a group are the names that its members reach, or are, and that are no groups.

# the versions of a store, and the store: the graph of its groups
type Graph is Data:
  Graph{versions: List<&2, Types.Entry>, store: Hashes.Hash}

# the members of the name v in g (none: v is no group)
def Graph.succ(g: Graph, v: String) -> List<&2, String>:
  match g:
    case Graph{es, s}:
      Groups.list(Groups.mem(es, s, v))

# rest, after the name of the group that r sets, when r is a Group
def Request.named(r: Spec.Request, rest: List<&2, String>) -> List<&2, String>:
  match r:
    case Spec.Request.Group{s, g, ms}:
      g <> rest
    case o:
      rest

# the name of the group of each Group version of es
def Groups.names(es: List<&2, Types.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{e, t}:
      Request.named(Entry.request(e), Groups.names(t))

# the names that have members in g: those of its Group versions
def Graph.nodes(g: Graph) -> List<&2, String>:
  match g:
    case Graph{es, s}:
      Groups.names(es)

# the names of xs that are no groups of the store s, by the versions es
def Groups.leaves(
  xs: List<&2, String>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, t}:
      List.filter.put(
        String,
        x,
        Groups.leaves(t, es, s),
        Bool.not(Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, x)))
      )

# the nodes of the members ms, by the versions es of the store s, each once
# when ms holds each once: the names that are no groups, among ms and what
# they reach
def Groups.reach(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  ms: List<&2, String>
) -> List<&2, String>:
  Groups.leaves(
    Closure.of(~String, ~Graph, ~String.eq, ~Graph.succ, ~Graph.nodes, Graph{es, s}, ms),
    es,
    s
  )

# the members of the group g of the store s, by the versions es (none: g is
# no group)
def Groups.members.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String
) -> Maybe<&2, List<&2, String>>:
  Groups.mem(es, s, g)

# whether g is a group of the store s, by the versions es
def Groups.is_group.of(+es: List<&2, Types.Entry>, +s: Hashes.Hash, g: String) -> Maybe<&2, Bool>:
  Some{Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, g))}

# the nodes of a group, when the name is one (mv is its members)
def Groups.nodes.pick(
  mv: Maybe<&2, List<&2, String>>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> Maybe<&2, List<&2, String>>:
  match mv:
    case None{}:
      None{}
    case Some{ms}:
      Some{Groups.reach(es, s, ms)}

# the nodes of the group g of the store s, by the versions es (none: g is no
# group)
def Groups.nodes.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String
) -> Maybe<&2, List<&2, String>>:
  Groups.nodes.pick(Groups.mem(es, s, g), es, s)

# the members of the group g of the store s at the version m of r (none: g is
# no group)
def Groups.members(
  r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String,
  m: Nat
) -> Maybe<&2, List<&2, String>>:
  Groups.members.of(List.take(&2, Types.Entry, r, 1n+m), s, g)

# whether g is a group of the store s at the version m of r
def Groups.is_group(
  r: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  g: String,
  m: Nat
) -> Maybe<&2, Bool>:
  Groups.is_group.of(List.take(&2, Types.Entry, r, 1n+m), s, g)

# the nodes of the group g of the store s at the version m of r: its members
# that are no groups, and the nodes of its members that are groups (none: g is
# no group)
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
    Groups.mem_last(List.take(&2, Types.Entry, r, 1n+m), s, g, ms, h)
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
        h
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
        Shared.Maybe.some_inj(Bool, Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, g)), False{}, h))
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

# what a list holds, it holds with x put before it, or not
def Groups.put_keeps(
  b: Bool,
  +x: String,
  +rest: List<&2, String>,
  +v: String
) -> {
  List.contains(~String, ~String.eq, rest, v) == True{}: Bool
} -> {List.contains(~String, ~String.eq, List.filter.put(String, x, rest, b), v) == True{}: Bool}:
  match b:
    case False{}:
      h => h
    case True{}:
      h => Shared.List.contains_cons(~String, ~String.eq, x, rest, v)(h)

# Groups.leaves_keeps at the first name x, by whether it is v (hit)
def Groups.leaves_keeps.at(
  +hit: Bool,
  +x: String,
  +t: List<&2, String>,
  +v: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  ih: {
    List.contains(~String, ~String.eq, t, v) == True{}: Bool
  } -> {
    Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>
  } -> {List.contains(~String, ~String.eq, Groups.leaves(t, es, s), v) == True{}: Bool}
) -> {
  String.eq(x, v) == hit: Bool
} -> {
  List.any.if(u => List.contains(~String, ~String.eq, t, v), hit) == True{}: Bool
} -> {
  Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>
} -> {
  List.contains(
    ~String,
    ~String.eq,
    List.filter.put(
      String,
      x,
      Groups.leaves(t, es, s),
      Bool.not(Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, x)))
    ),
    v
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      +he => h => hv =>
        %Equal.sym(
          Maybe<&2, List<&2, String>>,
          Groups.mem(es, s, x),
          None{},
          Equal.trans(
            Maybe<&2, List<&2, String>>,
            Groups.mem(es, s, x),
            Groups.mem(es, s, v),
            None{},
            Equal.cong(
              String,
              Maybe<&2, List<&2, String>>,
              z => Groups.mem(es, s, z),
              x,
              v,
              Texts.String.eq_sound(x, v)(he)
            ),
            hv
          )
        ): {
          List.contains(
            ~String,
            ~String.eq,
            List.filter.put(
              String,
              x,
              Groups.leaves(t, es, s),
              Bool.not(Maybe.is_some(&2, List<&2, String>, _))
            ),
            v
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          String.eq(x, v),
          True{},
          he
        ): {
          List.any.if(
            u => List.contains(~String, ~String.eq, Groups.leaves(t, es, s), v),
            _
          )
            == True{}: Bool
        }
        {==}
    case False{}:
      he => h => hv => Groups.put_keeps(
        Bool.not(Maybe.is_some(&2, List<&2, String>, Groups.mem(es, s, x))),
        x,
        Groups.leaves(t, es, s),
        v
      )(ih(h)(hv))

# a name of xs that is no group is among the leaves of xs
def Groups.leaves_keeps(
  +xs: List<&2, String>,
  +v: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> {
  List.contains(~String, ~String.eq, xs, v) == True{}: Bool
} -> {
  Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>
} -> {List.contains(~String, ~String.eq, Groups.leaves(xs, es, s), v) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => hv => Empty.absurd(
        {List.contains(~String, ~String.eq, [], v) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +t}:
      h => hv => Groups.leaves_keeps.at(
        String.eq(x, v),
        x,
        t,
        v,
        es,
        s,
        Groups.leaves_keeps(t, v, es, s)
      )({==})(h)(hv)

# Groups.leaves_only at the first name x, by whether it is a group (mx) and
# whether it is v (hit)
def Groups.leaves_only.at(
  mx: Maybe<&2, List<&2, String>>,
  +hit: Bool,
  +x: String,
  +t: List<&2, String>,
  +v: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  ih: {
    List.contains(~String, ~String.eq, Groups.leaves(t, es, s), v) == True{}: Bool
  } -> {
    List.contains(~String, ~String.eq, t, v) == True{}: Bool
  }
    & {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>}
) -> {
  Groups.mem(es, s, x) == mx: Maybe<&2, List<&2, String>>
} -> {
  String.eq(x, v) == hit: Bool
} -> {
  List.contains(
    ~String,
    ~String.eq,
    List.filter.put(
      String,
      x,
      Groups.leaves(t, es, s),
      Bool.not(Maybe.is_some(&2, List<&2, String>, mx))
    ),
    v
  )
    == True{}: Bool
} -> {
  List.any.if(u => List.contains(~String, ~String.eq, t, v), hit) == True{}: Bool
}
  & {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>}:
  match mx hit:
    case None{} True{}:
      hm => he => h => (
        {==},
        Equal.trans(
          Maybe<&2, List<&2, String>>,
          Groups.mem(es, s, v),
          Groups.mem(es, s, x),
          None{},
          Equal.cong(
            String,
            Maybe<&2, List<&2, String>>,
            z => Groups.mem(es, s, z),
            v,
            x,
            Equal.sym(String, x, v, Texts.String.eq_sound(x, v)(he))
          ),
          hm
        )
      )
    case None{} False{}:
      hm => he => h => ih(
        (%he: {
          List.any.if(
            u => List.contains(~String, ~String.eq, Groups.leaves(t, es, s), v),
            _
          )
            == True{}: Bool
        }
          h)
      )
    case Some{ms} True{}:
      hm => he => h =>
        (
          {==},
          Pair.snd(
            {List.contains(~String, ~String.eq, t, v) == True{}: Bool},
            {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>},
            ih(h)
          )
        )
    case Some{ms} False{}:
      hm => he => h => ih(h)

# a leaf of xs is a name of xs that is no group
def Groups.leaves_only(
  +xs: List<&2, String>,
  +v: String,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash
) -> {
  List.contains(~String, ~String.eq, Groups.leaves(xs, es, s), v) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, xs, v) == True{}: Bool
}
  & {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>}:
  match xs:
    case Nil{}:
      h => Empty.absurd(
        {
          List.contains(~String, ~String.eq, [], v) == True{}: Bool
        }
          & {Groups.mem(es, s, v) == None{}: Maybe<&2, List<&2, String>>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +t}:
      h => Groups.leaves_only.at(
        Groups.mem(es, s, x),
        String.eq(x, v),
        x,
        t,
        v,
        es,
        s,
        Groups.leaves_only(t, v, es, s)
      )({==})({==})(h)

# what the names hold, they hold with the name that a request sets
def Groups.named_keeps(
  r: Spec.Request,
  +g: String,
  +rest: List<&2, String>
) -> {
  List.contains(~String, ~String.eq, rest, g) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Request.named(r, rest), g) == True{}: Bool}:
  match r:
    case Spec.Request.Start{o}:
      h => h
    case Spec.Request.Write{b, p, w}:
      h => h
    case Spec.Request.Merge{f, i}:
      h => h
    case Spec.Request.Resolve{i, p, w}:
      h => h
    case Spec.Request.Mark{b, n, v}:
      h => h
    case Spec.Request.Move{b, t, v}:
      h => h
    case Spec.Request.Own{c2, g3}:
      h => h
    case Spec.Request.Group{s2, +g2, ms}:
      h => Shared.List.contains_cons(~String, ~String.eq, g2, rest, g)(h)

# the name of a Group version is among the names of the groups
def Groups.names_at(
  +es: List<&2, Types.Entry>,
  +j: Nat,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  a: Groups.At(es, j, Spec.Request.Group{s, g, ms})
) -> {List.contains(~String, ~String.eq, Groups.names(es), g) == True{}: Bool}:
  match es j:
    case Nil{} k:
      Empty.absurd(
        {List.contains(~String, ~String.eq, [], g) == True{}: Bool},
        Groups.At.nil(k, Spec.Request.Group{s, g, ms}, a)
      )
    case Con{+e0, +t} 0n:
      (+e, p) = a
      (hg, hr) = p
      %Equal.sym(
        Spec.Request,
        Entry.request(e0),
        Spec.Request.Group{s, g, ms},
        Equal.trans(
          Spec.Request,
          Entry.request(e0),
          Entry.request(e),
          Spec.Request.Group{s, g, ms},
          Equal.cong(
            Types.Entry,
            Spec.Request,
            z => Entry.request(z),
            e0,
            e,
            Shared.Maybe.some_inj(Types.Entry, e0, e, hg)
          ),
          hr
        )
      ): {List.contains(~String, ~String.eq, Request.named(_, Groups.names(t)), g) == True{}: Bool}
      Names.contains_first(g, Groups.names(t))
    case Con{+e0, +t} 1n+k:
      Groups.named_keeps(Entry.request(e0), g, Groups.names(t))(Groups.names_at(t, k, s, g, ms, a))

# Graph.live, by the members of the name p (mv)
def Graph.live.at(
  mv: Maybe<&2, List<&2, String>>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +p: String,
  +q: String
) -> {
  Groups.mem(es, s, p) == mv: Maybe<&2, List<&2, String>>
} -> {
  List.contains(~String, ~String.eq, Groups.list(mv), q) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Groups.names(es), p) == True{}: Bool}:
  match mv:
    case None{}:
      he => h => Empty.absurd(
        {List.contains(~String, ~String.eq, Groups.names(es), p) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{+ms}:
      he => h => Exists.use(
        Nat,
        j => Groups.At(es, j, Spec.Request.Group{s, p, ms}),
        {List.contains(~String, ~String.eq, Groups.names(es), p) == True{}: Bool},
        Groups.Last.at(
          es,
          Seek.Group{s, p},
          Spec.Request.Group{s, p, ms},
          Groups.mem_last(es, s, p, ms, he)
        ),
        +j => a => Groups.names_at(es, j, s, p, ms, a)
      )

# Graph.live, for the versions es of the store s
def Graph.live.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +p: String,
  +q: String
) -> {
  List.contains(~String, ~String.eq, Groups.list(Groups.mem(es, s, p)), q) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Groups.names(es), p) == True{}: Bool}:
  h => Graph.live.at(Groups.mem(es, s, p), es, s, p, q)({==})(h)

# a name with a member has a Group version: it is a node of the graph
def Graph.live(
  g: Graph,
  p: String,
  q: String
) -> {
  List.contains(~String, ~String.eq, Graph.succ(g, p), q) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Graph.nodes(g), p) == True{}: Bool}:
  match g:
    case Graph{es, s}:
      h => Graph.live.of(es, s, p, q)(h)

# the end of a path from the members ms that is no group is a node of theirs
def Groups.reach_in(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +ps: List<&2, String>,
  +x: String
) -> {
  Reaches.Reach.path(
    ~String,
    ~Graph,
    ~String.eq,
    ~Graph.succ,
    ps,
    ms,
    Graph{es, s},
    x
  )
    == True{}: Bool
} -> {
  Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>
} -> {List.contains(~String, ~String.eq, Groups.reach(es, s, ms), x) == True{}: Bool}:
  h => hv => Groups.leaves_keeps(
    Closure.of(~String, ~Graph, ~String.eq, ~Graph.succ, ~Graph.nodes, Graph{es, s}, ms),
    x,
    es,
    s
  )(
    Closure.path_of(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ~Graph.nodes,
      ~Texts.String.laws(),
      ~Graph.live,
      Graph{es, s},
      ms,
      ps,
      x
    )(h)
  )(hv)

# Groups.reach_out, once x is known to be a leaf of what ms reaches
def Groups.reach_out.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  w: {
    List.contains(
      ~String,
      ~String.eq,
      Closure.of(~String, ~Graph, ~String.eq, ~Graph.succ, ~Graph.nodes, Graph{es, s}, ms),
      x
    )
      == True{}: Bool
  }
    & {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}
) -> (
  &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ps,
      ms,
      Graph{es, s},
      x
    )
      == True{}: Bool
  }
)
  & {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}:
  (hc, hn) = w
  (
    Closure.of_path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ~Graph.nodes,
      ~Texts.String.laws(),
      Graph{es, s},
      ms,
      x
    )(hc),
    hn
  )

# a node of the members ms has a path from ms, and is no group
def Groups.reach_out(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String
) -> {
  List.contains(~String, ~String.eq, Groups.reach(es, s, ms), x) == True{}: Bool
} -> (
  &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ps,
      ms,
      Graph{es, s},
      x
    )
      == True{}: Bool
  }
)
  & {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}:
  h => Groups.reach_out.of(
    es,
    s,
    ms,
    x,
    Groups.leaves_only(
      Closure.of(~String, ~Graph, ~String.eq, ~Graph.succ, ~Graph.nodes, Graph{es, s}, ms),
      x,
      es,
      s
    )(h)
  )

# the nodes of a group are those of its members
def Groups.nodes_some(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>}
) -> {Groups.nodes.of(es, s, g) == Some{Groups.reach(es, s, ms)}: Maybe<&2, List<&2, String>>}:
  %Equal.sym(
    Maybe<&2, List<&2, String>>,
    Groups.mem(es, s, g),
    Some{ms},
    hm
  ): {Groups.nodes.pick(_, es, s) == Some{Groups.reach(es, s, ms)}: Maybe<&2, List<&2, String>>}
  {==}

# Groups.nodes_mem, by the members of the name g (mv)
def Groups.nodes_mem.at(
  mv: Maybe<&2, List<&2, String>>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ns: List<&2, String>
) -> {
  Groups.mem(es, s, g) == mv: Maybe<&2, List<&2, String>>
} -> {
  Groups.nodes.pick(mv, es, s) == Some{ns}: Maybe<&2, List<&2, String>>
} -> Exists(
  List<&2, String>,
  ms => {
    Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>
  }
    & {Groups.reach(es, s, ms) == ns: List<&2, String>}
):
  match mv:
    case None{}:
      he => h => Empty.absurd(
        Exists(
          List<&2, String>,
          ms => {
            Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>
          }
            & {Groups.reach(es, s, ms) == ns: List<&2, String>}
        ),
        Shared.Maybe.none_ne_some(List<&2, String>, ns, h)
      )
    case Some{+ms}:
      he => h => (ms, (he, Shared.Maybe.some_inj(List<&2, String>, Groups.reach(es, s, ms), ns, h)))

# a name with nodes is a group, and they are the nodes of its members
def Groups.nodes_mem(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ns: List<&2, String>,
  h: {Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>}
) -> Exists(
  List<&2, String>,
  ms => {
    Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>
  }
    & {Groups.reach(es, s, ms) == ns: List<&2, String>}
):
  Groups.nodes_mem.at(Groups.mem(es, s, g), es, s, g, ns)({==})(h)

# Groups.nodes_member, from the members that were found
def Groups.nodes_member.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
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
    Groups.reach(es, s, ms),
    (Groups.nodes_some(es, s, g, ms, hm), Groups.reach_in(es, s, ms, [], v)(h2)(hv))
  )

# Groups.nodes_nested, once the path from the members of v to x is found
def Groups.nodes_nested.path(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  +x: String,
  +vm: List<&2, String>,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  hvm: {Groups.mem(es, s, v) == Some{vm}: Maybe<&2, List<&2, String>>},
  hn: {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>},
  pv: &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ps,
      vm,
      Graph{es, s},
      x
    )
      == True{}: Bool
  }
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  match pv:
    case (+ps, hp):
      (
        Groups.reach(es, s, ms),
        (
          Groups.nodes_some(es, s, g, ms, hm),
          Groups.reach_in(
            es,
            s,
            ms,
            v <> ps,
            x
          )(
            Shared.Bool.and_both(
              List.contains(~String, ~String.eq, ms, v),
              Reaches.Reach.path(
                ~String,
                ~Graph,
                ~String.eq,
                ~Graph.succ,
                ps,
                Groups.list(Groups.mem(es, s, v)),
                Graph{es, s},
                x
              )
            )(
              h2
            )(
              (%Equal.sym(
                Maybe<&2, List<&2, String>>,
                Groups.mem(es, s, v),
                Some{vm},
                hvm
              ): {
                Reaches.Reach.path(
                  ~String,
                  ~Graph,
                  ~String.eq,
                  ~Graph.succ,
                  ps,
                  Groups.list(_),
                  Graph{es, s},
                  x
                )
                  == True{}: Bool
              }
                hp)
            )
          )(hn)
        )
      )

# Groups.nodes_nested, once x is known to be a node of the members of v
def Groups.nodes_nested.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  +x: String,
  +vm: List<&2, String>,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  hvm: {Groups.mem(es, s, v) == Some{vm}: Maybe<&2, List<&2, String>>},
  w: (
    &ps: List<
      &2,
      String> -> {
      Reaches.Reach.path(
        ~String,
        ~Graph,
        ~String.eq,
        ~Graph.succ,
        ps,
        vm,
        Graph{es, s},
        x
      )
        == True{}: Bool
    }
  )
    & {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  (pv, hn) = w
  Groups.nodes_nested.path(es, s, g, ms, v, x, vm, hm, h2, hvm, hn, pv)

# Groups.nodes_nested, from the members that were found
def Groups.nodes_nested.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +g: String,
  +ms: List<&2, String>,
  +v: String,
  +x: String,
  +vm: List<&2, String>,
  hm: {Groups.mem(es, s, g) == Some{ms}: Maybe<&2, List<&2, String>>},
  h2: {List.contains(~String, ~String.eq, ms, v) == True{}: Bool},
  hvm: {Groups.mem(es, s, v) == Some{vm}: Maybe<&2, List<&2, String>>},
  hx: {List.contains(~String, ~String.eq, Groups.reach(es, s, vm), x) == True{}: Bool}
) -> Exists(
  List<&2, String>,
  ns => {
    Groups.nodes.of(es, s, g) == Some{ns}: Maybe<&2, List<&2, String>>
  }
    & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
):
  Groups.nodes_nested.of(es, s, g, ms, v, x, vm, hm, h2, hvm, Groups.reach_out(es, s, vm, x)(hx))

# how the member v gives the node x: it is x and no group, or it is a group
# with the node x
def Groups.Via(es: List<&2, Types.Entry>, s: Hashes.Hash, v: String, x: String) -> Type:
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

# Groups.nodes_only at the first name p of the path, by its members (mv)
def Groups.nodes_only.at(
  mv: Maybe<&2, List<&2, String>>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  +p: String,
  +r: List<&2, String>,
  hc: {List.contains(~String, ~String.eq, ms, p) == True{}: Bool}
) -> {
  Groups.mem(es, s, p) == mv: Maybe<&2, List<&2, String>>
} -> {
  Reaches.Reach.path(
    ~String,
    ~Graph,
    ~String.eq,
    ~Graph.succ,
    r,
    Groups.list(mv),
    Graph{es, s},
    x
  )
    == True{}: Bool
} -> {
  List.contains(
    ~String,
    ~String.eq,
    Groups.list(mv),
    Reaches.Reach.first(String, r, x)
  )
    == True{}: Bool
} -> {
  Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>
} -> Exists(
  String,
  v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
):
  match mv:
    case None{}:
      he => hp => hf => hn => Empty.absurd(
        Exists(
          String,
          v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
        ),
        Shared.Bool.false_ne_true(hf)
      )
    case Some{+vm}:
      +he => hp => hf => hn => (
        p,
        (
          hc,
          Inr{
            (
              (%Equal.sym(
                Maybe<&2, List<&2, String>>,
                Groups.mem(es, s, p),
                Some{vm},
                he
              ): {Some{Maybe.is_some(&2, List<&2, String>, _)} == Some{True{}}: Maybe<&2, Bool>}
                {==}),
              (
                Groups.reach(es, s, vm),
                (Groups.nodes_some(es, s, p, vm, he), Groups.reach_in(es, s, vm, r, x)(hp)(hn))
              )
            )
          }
        )
      )

# Groups.nodes_only, by the path ps from the members to x
def Groups.nodes_only.by(
  ps: List<&2, String>,
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  +hp: {
    Reaches.Reach.path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ps,
      ms,
      Graph{es, s},
      x
    )
      == True{}: Bool
  },
  hn: {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}
) -> Exists(
  String,
  v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
):
  match ps:
    case Nil{}:
      (
        x,
        (
          hp,
          Inl{
            (
              Texts.String.eq_refl(x),
              (%Equal.sym(
                Maybe<&2, List<&2, String>>,
                Groups.mem(es, s, x),
                None{},
                hn
              ): {Some{Maybe.is_some(&2, List<&2, String>, _)} == Some{False{}}: Maybe<&2, Bool>}
                {==})
            )
          }
        )
      )
    case Con{+p, +r}:
      Groups.nodes_only.at(
        Groups.mem(es, s, p),
        es,
        s,
        ms,
        x,
        p,
        r,
        Shared.Bool.and_true_left(
          List.contains(~String, ~String.eq, ms, p),
          Reaches.Reach.path(
            ~String,
            ~Graph,
            ~String.eq,
            ~Graph.succ,
            r,
            Groups.list(Groups.mem(es, s, p)),
            Graph{es, s},
            x
          )
        )(hp)
      )(
        {==}
      )(
        Shared.Bool.and_true_right(
          List.contains(~String, ~String.eq, ms, p),
          Reaches.Reach.path(
            ~String,
            ~Graph,
            ~String.eq,
            ~Graph.succ,
            r,
            Groups.list(Groups.mem(es, s, p)),
            Graph{es, s},
            x
          )
        )(hp)
      )(
        Reaches.Reach.path_first(
          ~String,
          ~Graph,
          ~String.eq,
          ~Graph.succ,
          r,
          Groups.list(Groups.mem(es, s, p)),
          Graph{es, s},
          x
        )(
          Shared.Bool.and_true_right(
            List.contains(~String, ~String.eq, ms, p),
            Reaches.Reach.path(
              ~String,
              ~Graph,
              ~String.eq,
              ~Graph.succ,
              r,
              Groups.list(Groups.mem(es, s, p)),
              Graph{es, s},
              x
            )
          )(hp)
        )
      )(hn)

# Groups.nodes_only, once the path from the members to x is found
def Groups.nodes_only.path(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  hn: {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>},
  pv: &ps: List<
    &2,
    String> -> {
    Reaches.Reach.path(
      ~String,
      ~Graph,
      ~String.eq,
      ~Graph.succ,
      ps,
      ms,
      Graph{es, s},
      x
    )
      == True{}: Bool
  }
) -> Exists(
  String,
  v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
):
  match pv:
    case (ps, hp):
      Groups.nodes_only.by(ps, es, s, ms, x, hp, hn)

# Groups.nodes_only, once x is known to be a node of the members
def Groups.nodes_only.of(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  w: (
    &ps: List<
      &2,
      String> -> {
      Reaches.Reach.path(
        ~String,
        ~Graph,
        ~String.eq,
        ~Graph.succ,
        ps,
        ms,
        Graph{es, s},
        x
      )
        == True{}: Bool
    }
  )
    & {Groups.mem(es, s, x) == None{}: Maybe<&2, List<&2, String>>}
) -> Exists(
  String,
  v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
):
  (pv, hn) = w
  Groups.nodes_only.path(es, s, ms, x, hn, pv)

# Groups.nodes_only, from the members that were found
def Groups.nodes_only.core(
  +es: List<&2, Types.Entry>,
  +s: Hashes.Hash,
  +ms: List<&2, String>,
  +x: String,
  hx: {List.contains(~String, ~String.eq, Groups.reach(es, s, ms), x) == True{}: Bool}
) -> Exists(
  String,
  v => {List.contains(~String, ~String.eq, ms, v) == True{}: Bool} & Groups.Via(es, s, v, x)
):
  Groups.nodes_only.of(es, s, ms, x, Groups.reach_out(es, s, ms, x)(hx))

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
  Groups.nodes_member.core(
    List.take(&2, Types.Entry, r, 1n+m),
    s,
    g,
    ms,
    v,
    h1,
    h2,
    Maybe.is_some_false(
      List<&2, String>,
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v)
    )(
      Shared.Maybe.some_inj(
        Bool,
        Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v)),
        False{},
        h3
      )
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
  Exists.use(
    List<&2, String>,
    vm => {
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v) == Some{vm}: Maybe<&2, List<&2, String>>
    },
    Exists(
      List<&2, String>,
      ns => {
        Groups.nodes(r, s, g, m) == Some{ns}: Maybe<&2, List<&2, String>>
      }
        & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    ),
    Maybe.is_some_true(
      List<&2, String>,
      Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v)
    )(
      Shared.Maybe.some_inj(
        Bool,
        Maybe.is_some(&2, List<&2, String>, Groups.mem(List.take(&2, Types.Entry, r, 1n+m), s, v)),
        True{},
        h3
      )
    ),
    +vm => +hvm => Groups.nodes_nested.core(
      List.take(&2, Types.Entry, r, 1n+m),
      s,
      g,
      ms,
      v,
      x,
      vm,
      h1,
      h2,
      hvm,
      (%Equal.sym(
        List<&2, String>,
        Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, vm),
        vs,
        Shared.Maybe.some_inj(
          List<&2, String>,
          Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, vm),
          vs,
          Equal.trans(
            Maybe<&2, List<&2, String>>,
            Some{Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, vm)},
            Groups.nodes.of(List.take(&2, Types.Entry, r, 1n+m), s, v),
            Some{vs},
            Equal.sym(
              Maybe<&2, List<&2, String>>,
              Groups.nodes.of(List.take(&2, Types.Entry, r, 1n+m), s, v),
              Some{Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, vm)},
              Groups.nodes_some(List.take(&2, Types.Entry, r, 1n+m), s, v, vm, hvm)
            ),
            h4
          )
        )
      ): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
        h5)
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
    }
      & {Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, ms) == ns: List<&2, String>},
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
    +ms => w => (
      ms,
      Pair.use(
        {
          Groups.mem(
            List.take(&2, Types.Entry, r, 1n+m),
            s,
            g
          )
            == Some{ms}: Maybe<&2, List<&2, String>>
        },
        {Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, ms) == ns: List<&2, String>},
        {
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
          ),
        w,
        hm => hr => (
          hm,
          Groups.nodes_only.core(
            List.take(&2, Types.Entry, r, 1n+m),
            s,
            ms,
            x,
            (%Equal.sym(
              List<&2, String>,
              Groups.reach(List.take(&2, Types.Entry, r, 1n+m), s, ms),
              ns,
              hr
            ): {List.contains(~String, ~String.eq, _, x) == True{}: Bool}
              h2)
          )
        )
      )
    )
  )
