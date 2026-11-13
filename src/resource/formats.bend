import Base
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/side.bend as Sides
import ../shared/shared/shared/text.bend as Texts

# Forks
# -----
# Where two lists agree from the start (a fork), and where they agree to the
# end (their ends), as same calls their elements equal.

# the start that two lists share (same), then the rest of each (a and b)
type Fork<-A: Data> is Data:
  Fork{same: List<&2, A>, a: List<&2, A>, b: List<&2, A>}

# the first list of a fork, again
def Fork.left(-A: Data, f: Fork<A>) -> List<&2, A>:
  match f:
    case Fork{s, a, b}:
      List.append(&2, A, s, a)

# the second list of a fork, again
def Fork.right(-A: Data, f: Fork<A>) -> List<&2, A>:
  match f:
    case Fork{s, a, b}:
      List.append(&2, A, s, b)

# the fork of x <> ra and y <> rb, by whether x and y are the same (held); f is
# the fork of ra and rb
def List.fork.on(
  -A: Data,
  held: Bool,
  x: A,
  y: A,
  ra: List<&2, A>,
  rb: List<&2, A>,
  f: Fork<A>
) -> Fork<A>:
  match held f:
    case True{} Fork{s, fa, fb}:
      Fork{x <> s, fa, fb}
    case False{} g:
      Fork{[], x <> ra, y <> rb}

# the start that a and b share, then the rest of each
def List.fork(~A: Data, ~same: A -> A -> Bool, a: List<&2, A>, b: List<&2, A>) -> Fork<A>:
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork.on(A, same(x, y), x, y, ra, rb, List.fork(~A, ~same, ra, rb))
    case Nil{} y:
      Fork{[], [], y}
    case Con{x, ra} Nil{}:
      Fork{[], x <> ra, []}

# Laws
# ----
# Each law asks of same only that it is True only for equal elements (sound).

# List.fork_left after the first elements
def List.fork_left.on(
  -A: Data,
  held: Bool,
  x: A,
  y: A,
  ra: List<&2, A>,
  rb: List<&2, A>,
  f: Fork<A>,
  ih: {Fork.left(A, f) == ra: List<&2, A>}
) -> {Fork.left(A, List.fork.on(A, held, x, y, ra, rb, f)) == x <> ra: List<&2, A>}:
  match held f:
    case True{} Fork{s, fa, fb}:
      %ih: {x <> List.append(&2, A, s, fa) == x <> _: List<&2, A>}
      {==}
    case False{} g:
      {==}

# a fork gives back the first list
def List.fork_left(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  a: List<&2, Ty>,
  b: List<&2, Ty>
) -> {Fork.left(Ty, List.fork(~Ty, ~same, a, b)) == a: List<&2, Ty>}:
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork_left.on(
        Ty,
        same(x, y),
        x,
        y,
        ra,
        rb,
        List.fork(~Ty, ~same, ra, rb),
        List.fork_left(~Ty, ~same, ra, rb)
      )
    case Nil{} y:
      {==}
    case Con{x, ra} Nil{}:
      {==}

# List.fork_right after the first elements
def List.fork_right.on(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  held: Bool,
  x: A,
  y: A,
  ra: List<&2, A>,
  rb: List<&2, A>,
  f: Fork<A>,
  e: {same(x, y) == held: Bool},
  ih: {Fork.right(A, f) == rb: List<&2, A>}
) -> {Fork.right(A, List.fork.on(A, held, x, y, ra, rb, f)) == y <> rb: List<&2, A>}:
  match held f:
    case True{} Fork{s, fa, fb}:
      append1 = List.append(&2, A, s, fb)
      %ih: {x <> append1 == y <> _: List<&2, A>}
      %Shared.Eq.sound(~A, ~same, laws, x)(y)(e): {x <> append1 == _ <> append1: List<&2, A>}
      {==}
    case False{} g:
      {==}

# a fork gives back the second list
def List.fork_right(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  a: List<&2, Ty>,
  b: List<&2, Ty>
) -> {Fork.right(Ty, List.fork(~Ty, ~same, a, b)) == b: List<&2, Ty>}:
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork_right.on(
        ~Ty,
        ~same,
        ~laws,
        same(x, y),
        x,
        y,
        ra,
        rb,
        List.fork(~Ty, ~same, ra, rb),
        {==},
        List.fork_right(~Ty, ~same, ~laws, ra, rb)
      )
    case Nil{} y:
      {==}
    case Con{x, ra} Nil{}:
      {==}

# Reversed lists
# --------------
# A fork of two lists reversed is where they agree to the end.

# reversing xs then ys onto acc, as two reversals
def List.reverse_append(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  -acc: List<&2, A>
) -> {
  List.reverse.go(
    &2,
    A,
    ys,
    List.reverse.go(&2, A, xs, acc)
  )
    == List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      List.reverse_append(A, r, ys, x <> acc)

# reversing xs onto a, then acc, is reversing xs onto a then acc
def List.reverse_onto(
  -A: Data,
  xs: List<&2, A>,
  -a: List<&2, A>,
  acc: List<&2, A>
) -> {
  List.reverse.go(
    &2,
    A,
    xs,
    List.append(&2, A, a, acc)
  )
    == List.append(&2, A, List.reverse.go(&2, A, xs, a), acc): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      List.reverse_onto(A, r, x <> a, acc)

# reversing xs onto acc, then reversing that, is acc reversed onto xs
def List.reverse_twice(
  -A: Data,
  xs: List<&2, A>,
  -acc: List<&2, A>
) -> {
  List.reverse.go(
    &2,
    A,
    acc,
    xs
  )
    == List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), []): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      List.reverse_twice(A, r, x <> acc)

# Formats
# -------
# A format reads a resource's bytes as parts, and says how two versions differ
# (a patch) and how two changes of one base merge. Lines is the default: the
# parts are the lines. Whole is for bytes that are not text (they hold a 0):
# the part is the whole content.

# Lines
# -----

# the lines of c then the bytes that split into s, by whether c is '\n' (nl)
def Lines.split.on(
  nl: Bool,
  c: U32,
  s: Texts.Bytes() & List<&2, Texts.Bytes()>
) -> Texts.Bytes()
  & List<&2, Texts.Bytes()>:
  match nl s:
    case True{} Tuple{l, ls}:
      ([], l <> ls)
    case False{} Tuple{l, ls}:
      (c <> l, ls)

# the lines of b, split at each '\n', as the line it starts with and the rest
def Lines.split(b: Texts.Bytes()) -> Texts.Bytes() & List<&2, Texts.Bytes()>:
  match b:
    case Nil{}:
      ([], [])
    case Con{+c, r}:
      Lines.split.on(U32.is_eq(c, 10), c, Lines.split(r))

# the bytes of the line l and then the lines ls, with a '\n' between each
def Lines.join(ls: List<&2, Texts.Bytes()>, l: Texts.Bytes()) -> Texts.Bytes():
  match ls:
    case Nil{}:
      l
    case Con{n, r}:
      List.append(&2, U32, l, 10 <> Lines.join(r, n))

# the bytes of a split
def Lines.join.of(s: Texts.Bytes() & List<&2, Texts.Bytes()>) -> Texts.Bytes():
  match s:
    case Tuple{l, ls}:
      Lines.join(ls, l)

# a byte before the first line comes first
def Lines.join_cons(
  ls: List<&2, Texts.Bytes()>,
  c: U32,
  l: Texts.Bytes()
) -> {Lines.join(ls, c <> l) == c <> Lines.join(ls, l): Texts.Bytes()}:
  match ls:
    case Nil{}:
      {==}
    case Con{n, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Lines.read_back once c is known to be '\n' or not (nl)
def Lines.read_back.on(
  nl: Bool,
  c: U32,
  s: Texts.Bytes() & List<&2, Texts.Bytes()>,
  r: Texts.Bytes(),
  e: {U32.is_eq(c, 10) == nl: Bool},
  ih: {Lines.join.of(s) == r: Texts.Bytes()}
) -> {Lines.join.of(Lines.split.on(nl, c, s)) == c <> r: Texts.Bytes()}:
  match nl s:
    case True{} Tuple{l, ls}:
      %Equal.sym(
        U32,
        c,
        10,
        Shared.U32.is_eq_sound(c, 10)(e)
      ): {10 <> Lines.join(ls, l) == _ <> r: Texts.Bytes()}
      %ih: {10 <> Lines.join(ls, l) == 10 <> _: Texts.Bytes()}
      {==}
    case False{} Tuple{l, ls}:
      %Equal.sym(
        Texts.Bytes(),
        Lines.join(ls, c <> l),
        c <> Lines.join(ls, l),
        Lines.join_cons(ls, c, l)
      ):
        {_ == c <> r: Texts.Bytes()}
      %ih: {c <> Lines.join(ls, l) == c <> _: Texts.Bytes()}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines of b join back into b
def Lines.read_back(b: Texts.Bytes()) -> {Lines.join.of(Lines.split(b)) == b: Texts.Bytes()}:
  match b:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      Lines.read_back.on(U32.is_eq(c, 10), c, Lines.split(r), r, {==}, Lines.read_back(r))

# Patches of lines
# ----------------

# a and b, cut into the lines that they share at the start, the lines that
# differ (old and new), and the lines that they share at the end
type Cut is Data:
  Cut{
    start: List<&2, Texts.Bytes()>,
    old: List<&2, Texts.Bytes()>,
    new: List<&2, Texts.Bytes()>,
    end: List<&2, Texts.Bytes()>
  }

# the old lines of c, between its start and end
def Cut.left(c: Cut) -> List<&2, Texts.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Texts.Bytes(), s, List.append(&2, Texts.Bytes(), o, e))

# the new lines of c, between its start and end
def Cut.right(c: Cut) -> List<&2, Texts.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Texts.Bytes(), s, List.append(&2, Texts.Bytes(), n, e))

# the cut with the start s, by the fork f of what follows it in each,
# reversed: the lines that differ, then the end that they share
def Lines.cut.back(s: List<&2, Texts.Bytes()>, f: Fork<Texts.Bytes()>) -> Cut:
  match f:
    case Fork{e, a, b}:
      Cut{
        s,
        List.reverse(&2, Texts.Bytes(), a),
        List.reverse(&2, Texts.Bytes(), b),
        List.reverse(&2, Texts.Bytes(), e)
      }

# the cut of a fork: what follows its shared start, forked again from the end
def Lines.cut.of(f: Fork<Texts.Bytes()>) -> Cut:
  match f:
    case Fork{s, ra, rb}:
      Lines.cut.back(
        s,
        List.fork(
          ~Texts.Bytes(),
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          List.reverse(&2, Texts.Bytes(), ra),
          List.reverse(&2, Texts.Bytes(), rb)
        )
      )

# the lines that a and b share at the start and at the end, and what differs
def Lines.cut(a: List<&2, Texts.Bytes()>, b: List<&2, Texts.Bytes()>) -> Cut:
  Lines.cut.of(List.fork(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b))

# the old lines of a cut from the end are its start, then the fork's first
# list, reversed
def Lines.cut.back_left(
  s: List<&2, Texts.Bytes()>,
  f: Fork<Texts.Bytes()>
) -> {
  List.append(
    &2,
    Texts.Bytes(),
    s,
    List.reverse(&2, Texts.Bytes(), Fork.left(Texts.Bytes(), f))
  )
    == Cut.left(Lines.cut.back(s, f)): List<&2, Texts.Bytes()>
}:
  match f:
    case Fork{+e, a, b}:
      reverse1 = List.reverse(&2, Texts.Bytes(), e)
      %List.reverse_append(Texts.Bytes(), e, a, []):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            _
          )
            == Cut.left(Lines.cut.back(s, Fork{e, a, b})): List<&2, Texts.Bytes()>
        }
      %List.reverse_onto(Texts.Bytes(), a, [], reverse1):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            List.reverse.go(&2, Texts.Bytes(), a, reverse1)
          )
            == List.append(&2, Texts.Bytes(), s, _): List<&2, Texts.Bytes()>
        }
      {==}

# the new lines of a cut from the end are its start, then the fork's second
# list, reversed
def Lines.cut.back_right(
  s: List<&2, Texts.Bytes()>,
  f: Fork<Texts.Bytes()>
) -> {
  List.append(
    &2,
    Texts.Bytes(),
    s,
    List.reverse(&2, Texts.Bytes(), Fork.right(Texts.Bytes(), f))
  )
    == Cut.right(Lines.cut.back(s, f)): List<&2, Texts.Bytes()>
}:
  match f:
    case Fork{+e, a, b}:
      reverse1 = List.reverse(&2, Texts.Bytes(), e)
      %List.reverse_append(Texts.Bytes(), e, b, []):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            _
          )
            == Cut.right(Lines.cut.back(s, Fork{e, a, b})): List<&2, Texts.Bytes()>
        }
      %List.reverse_onto(Texts.Bytes(), b, [], reverse1):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            List.reverse.go(&2, Texts.Bytes(), b, reverse1)
          )
            == List.append(&2, Texts.Bytes(), s, _): List<&2, Texts.Bytes()>
        }
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the old lines of the cut of a fork are its first list
def Lines.cut.of_left(
  f: Fork<Texts.Bytes()>
) -> {Cut.left(Lines.cut.of(f)) == Fork.left(Texts.Bytes(), f): List<&2, Texts.Bytes()>}:
  match f:
    case Fork{+s, +ra, rb}:
      append1 = List.append(&2, Texts.Bytes(), s, ra)
      +reverse1 = List.reverse(&2, Texts.Bytes(), ra)
      +reverse2 = List.reverse(&2, Texts.Bytes(), rb)
      g = List.fork(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), reverse1, reverse2)
      %Lines.cut.back_left(s, g): {_ == append1: List<&2, Texts.Bytes()>}
      %Equal.sym(
        List<&2, Texts.Bytes()>,
        Fork.left(Texts.Bytes(), g),
        reverse1,
        List.fork_left(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), reverse1, reverse2)
      ):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            List.reverse(&2, Texts.Bytes(), _)
          )
            == append1: List<&2, Texts.Bytes()>
        }
      %List.reverse_twice(Texts.Bytes(), ra, []):
        {List.append(&2, Texts.Bytes(), s, _) == append1: List<&2, Texts.Bytes()>}
      {==}

# the new lines of the cut of a fork are its second list
def Lines.cut.of_right(
  f: Fork<Texts.Bytes()>
) -> {Cut.right(Lines.cut.of(f)) == Fork.right(Texts.Bytes(), f): List<&2, Texts.Bytes()>}:
  match f:
    case Fork{+s, ra, +rb}:
      append1 = List.append(&2, Texts.Bytes(), s, rb)
      +reverse1 = List.reverse(&2, Texts.Bytes(), rb)
      +reverse2 = List.reverse(&2, Texts.Bytes(), ra)
      g = List.fork(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), reverse2, reverse1)
      %Lines.cut.back_right(s, g): {_ == append1: List<&2, Texts.Bytes()>}
      %Equal.sym(
        List<&2, Texts.Bytes()>,
        Fork.right(Texts.Bytes(), g),
        reverse1,
        List.fork_right(
          ~Texts.Bytes(),
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
          reverse2,
          reverse1
        )
      ):
        {
          List.append(
            &2,
            Texts.Bytes(),
            s,
            List.reverse(&2, Texts.Bytes(), _)
          )
            == append1: List<&2, Texts.Bytes()>
        }
      %List.reverse_twice(Texts.Bytes(), rb, []):
        {List.append(&2, Texts.Bytes(), s, _) == append1: List<&2, Texts.Bytes()>}
      {==}

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the old lines
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_left(
  +a: List<&2, Texts.Bytes()>,
  +b: List<&2, Texts.Bytes()>
) -> {Cut.left(Lines.cut(a, b)) == a: List<&2, Texts.Bytes()>}:
  f = List.fork(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)
  Equal.trans(
    List<&2, Texts.Bytes()>,
    Cut.left(Lines.cut.of(f)),
    Fork.left(Texts.Bytes(), f),
    a,
    Lines.cut.of_left(f),
    List.fork_left(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the new lines
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_right(
  +a: List<&2, Texts.Bytes()>,
  +b: List<&2, Texts.Bytes()>
) -> {Cut.right(Lines.cut(a, b)) == b: List<&2, Texts.Bytes()>}:
  f = List.fork(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)
  Equal.trans(
    List<&2, Texts.Bytes()>,
    Cut.right(Lines.cut.of(f)),
    Fork.right(Texts.Bytes(), f),
    b,
    Lines.cut.of_right(f),
    List.fork_right(
      ~Texts.Bytes(),
      ~Shared.List.is_eq(~U32, ~U32.is_eq),
      ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
      a,
      b
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines a after a patch: keep the first keep lines, drop the next drop, and
# put the lines put in their place
def Lines.apply(
  keep: Nat,
  a: List<&2, Texts.Bytes()>,
  drop: Nat,
  put: List<&2, Texts.Bytes()>
) -> List<&2, Texts.Bytes()>:
  match keep a:
    case 0n x:
      List.append(&2, Texts.Bytes(), put, List.drop(&2, Texts.Bytes(), x, drop))
    case 1n+k Nil{}:
      put
    case 1n+k Con{l, r}:
      l <> Lines.apply(k, r, drop, put)

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# applying the patch of a cut to its old lines gives its new lines
def Lines.apply_cut(
  s: List<&2, Texts.Bytes()>,
  +o: List<&2, Texts.Bytes()>,
  +n: List<&2, Texts.Bytes()>,
  +e: List<&2, Texts.Bytes()>
) -> {
  Lines.apply(
    List.length(&2, Texts.Bytes(), s),
    Cut.left(Cut{s, o, n, e}),
    List.length(&2, Texts.Bytes(), o),
    n
  )
    == Cut.right(Cut{s, o, n, e}): List<&2, Texts.Bytes()>
}:
  match s:
    case Nil{}:
      %Equal.sym(
        List<&2, Texts.Bytes()>,
        List.drop(
          &2,
          Texts.Bytes(),
          List.append(&2, Texts.Bytes(), o, e),
          List.length(&2, Texts.Bytes(), o)
        ),
        e,
        Shared.List.drop_after_append(Texts.Bytes(), o, e)
      ):
        {
          List.append(
            &2,
            Texts.Bytes(),
            n,
            _
          )
            == List.append(&2, Texts.Bytes(), n, e): List<&2, Texts.Bytes()>
        }
      {==}
    case Con{l, +r}:
      right1 = Cut.right(Cut{r, o, n, e})
      %Equal.sym(
        List<&2, Texts.Bytes()>,
        Lines.apply(
          List.length(&2, Texts.Bytes(), r),
          Cut.left(Cut{r, o, n, e}),
          List.length(&2, Texts.Bytes(), o),
          n
        ),
        right1,
        Lines.apply_cut(r, o, n, e)
      ):
        {l <> _ == l <> right1: List<&2, Texts.Bytes()>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the lines of b
def Lines.list.of(s: Texts.Bytes() & List<&2, Texts.Bytes()>) -> List<&2, Texts.Bytes()>:
  match s:
    case Tuple{l, ls}:
      l <> ls

# the lines of b, as a list
def Lines.list(b: Texts.Bytes()) -> List<&2, Texts.Bytes()>:
  Lines.list.of(Lines.split(b))

# the bytes of the lines ls
def Lines.bytes(ls: List<&2, Texts.Bytes()>) -> Texts.Bytes():
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      Lines.join(r, l)

# the bytes of a split are the bytes of its lines
def Lines.bytes_of(
  s: Texts.Bytes() & List<&2, Texts.Bytes()>
) -> {Lines.bytes(Lines.list.of(s)) == Lines.join.of(s): Texts.Bytes()}:
  match s:
    case Tuple{l, ls}:
      {==}

# the lines of b give back b
def Lines.bytes_list(b: Texts.Bytes()) -> {Lines.bytes(Lines.list(b)) == b: Texts.Bytes()}:
  +b = b
  Equal.trans(
    Texts.Bytes(),
    Lines.bytes(Lines.list(b)),
    Lines.join.of(Lines.split(b)),
    b,
    Lines.bytes_of(Lines.split(b)),
    Lines.read_back(b)
  )

# Hunks
# -----
# A patch of lines is hunks, each after the last: keep some lines, drop some,
# put some in their place. A diff finds the fewest lines to drop and put
# (Myers): it walks the two lists of lines on each diagonal at once, so each
# step reads the next line of each, and its cost is the lines times the size
# of the change. Its hunks are checked against the new lines; a diff that
# does not check is the one cut of Lines.cut.

# a hunk: keep the next keep lines, drop the next drop, put the lines put
type Hunk is Data:
  Hunk{keep: Nat, drop: Nat, put: List<&2, Texts.Bytes()>}

# the lines a after the hunks hs, each after the last
def Lines.apply.all(hs: List<&2, Hunk>, +a: List<&2, Texts.Bytes()>) -> List<&2, Texts.Bytes()>:
  match hs:
    case Nil{}:
      a
    case Con{Hunk{+k, +d, put}, rest}:
      List.append(
        &2,
        Texts.Bytes(),
        List.take(&2, Texts.Bytes(), a, k),
        List.append(&2, Texts.Bytes(), put, Lines.apply.all(rest, List.drop(&2, Texts.Bytes(), a, Nat.add(k, d))))
      )

# the one hunk Hunk{k, d, put} is Lines.apply(k, a, d, put)
def Lines.apply.all_one(
  k: Nat,
  a: List<&2, Texts.Bytes()>,
  d: Nat,
  put: List<&2, Texts.Bytes()>
) -> {Lines.apply.all([Hunk{k, d, put}], a) == Lines.apply(k, a, d, put): List<&2, Texts.Bytes()>}:
  match k a:
    case 0n Nil{}:
      {==}
    case 0n Con{l, r}:
      {==}
    case 1n+p Nil{}:
      Shared.List.append_nil(Texts.Bytes(), put)
    case 1n+p Con{l, r}:
      %Lines.apply.all_one(p, r, d, put):
        {l <> Lines.apply.all([Hunk{p, d, put}], r) == l <> _: List<&2, Texts.Bytes()>}
      {==}

# a step of an edit: keep a line of both, drop a line of the old, or put a
# line of the new
type Op is Data:
  Op.Keep{}
  Op.Drop{}
  Op.Put{line: Texts.Bytes()}

# a walk of a diff: how many old lines it read (x), the old lines a and the
# new lines b left, and its steps, last first
type Walk is Data:
  Walk{x: Nat, a: List<&2, Texts.Bytes()>, b: List<&2, Texts.Bytes()>, ops: List<&2, Op>}

# the walk of x lines, on, while the next lines of a and b are the same
def Walk.snake(a: List<&2, Texts.Bytes()>, b: List<&2, Texts.Bytes()>, +x: Nat, +ops: List<&2, Op>) -> Walk:
  match a b:
    case Con{+la, +ra} Con{+lb, +rb}:
      Shared.Bool.when(
        Walk,
        Shared.List.is_eq(~U32, ~U32.is_eq, la, lb),
        u => Walk.snake(ra, rb, 1n+x, Op.Keep{} <> ops),
        u => Walk{x, la <> ra, lb <> rb, ops}
      )
    case xs ys:
      Walk{x, xs, ys, ops}

# the walk m with one old line dropped, then on as far as the lines agree
def Walk.drop(m: Maybe<&2, Walk>) -> Maybe<&2, Walk>:
  match m:
    case Some{Walk{x, Con{l, ra}, b, ops}}:
      Some{Walk.snake(ra, b, 1n+x, Op.Drop{} <> ops)}
    case _:
      None{}

# the walk m with one new line put, then on as far as the lines agree
def Walk.put(m: Maybe<&2, Walk>) -> Maybe<&2, Walk>:
  match m:
    case Some{Walk{x, a, Con{l, rb}, ops}}:
      Some{Walk.snake(a, rb, x, Op.Put{l} <> ops)}
    case _:
      None{}

# the walk of the two that read more old lines (a drop when they tie)
def Walk.best(d: Maybe<&2, Walk>, p: Maybe<&2, Walk>) -> Maybe<&2, Walk>:
  match d p:
    case Some{Walk{+x1, a1, b1, o1}} Some{Walk{+x2, a2, b2, o2}}:
      Shared.Bool.when(
        Maybe<&2, Walk>,
        Nat.is_lt(x1, x2),
        u => Some{Walk{x2, a2, b2, o2}},
        u => Some{Walk{x1, a1, b1, o1}}
      )
    case None{} q:
      q
    case q None{}:
      q

# the walks one step further, on each diagonal, from the walks ws of the
# diagonals below and the walk prev of the one before
def Walks.next(ws: List<&2, Maybe<&2, Walk>>, +prev: Maybe<&2, Walk>) -> List<&2, Maybe<&2, Walk>>:
  match ws:
    case Nil{}:
      [Walk.drop(prev)]
    case Con{+w, rest}:
      Walk.best(Walk.drop(prev), Walk.put(w)) <> Walks.next(rest, w)

# the steps of a walk among ws that read all of both lists
def Walks.done(ws: List<&2, Maybe<&2, Walk>>) -> Maybe<&2, List<&2, Op>>:
  match ws:
    case Nil{}:
      None{}
    case Con{Some{Walk{x, Nil{}, Nil{}, ops}}, rest}:
      Some{List.reverse(&2, Op, ops)}
    case Con{w, rest}:
      Walks.done(rest)

# Walks.go once it is known whether a walk is done (m)
def Walks.go.at(m: Maybe<&2, List<&2, Op>>, go: Unit -> Maybe<&2, List<&2, Op>>) -> Maybe<&2, List<&2, Op>>:
  match m:
    case Some{ops}:
      Some{ops}
    case None{}:
      go(Unit{})

# the steps of the first walks among ws, one step further at a time, that read
# all of both lists, at most f steps further
def Walks.go(f: Nat, +ws: List<&2, Maybe<&2, Walk>>) -> Maybe<&2, List<&2, Op>>:
  match f:
    case 0n:
      None{}
    case 1n+p:
      Walks.go.at(Walks.done(ws), u => Walks.go(p, Walks.next(ws, None{})))

# the fewest steps from the lines a to the lines b
def Lines.ops(+a: List<&2, Texts.Bytes()>, +b: List<&2, Texts.Bytes()>) -> Maybe<&2, List<&2, Op>>:
  Walks.go(
    1n+Nat.add(List.length(&2, Texts.Bytes(), a), List.length(&2, Texts.Bytes(), b)),
    [Some{Walk.snake(a, b, 0n, [])}]
  )

# the hunks of the steps ops, after k kept lines, d dropped lines and the put
# lines ps, last first
def Ops.hunks(ops: List<&2, Op>, +k: Nat, +d: Nat, +ps: List<&2, Texts.Bytes()>) -> List<&2, Hunk>:
  match ops:
    case Nil{}:
      Shared.Bool.when(
        List<&2, Hunk>,
        Bool.and(Nat.is_eq(d, 0n), List.is_empty(&2, Texts.Bytes(), ps)),
        u => [],
        u => [Hunk{k, d, List.reverse(&2, Texts.Bytes(), ps)}]
      )
    case Con{Op.Keep{}, +rest}:
      Shared.Bool.when(
        List<&2, Hunk>,
        Bool.and(Nat.is_eq(d, 0n), List.is_empty(&2, Texts.Bytes(), ps)),
        u => Ops.hunks(rest, 1n+k, 0n, []),
        u => Hunk{k, d, List.reverse(&2, Texts.Bytes(), ps)} <> Ops.hunks(rest, 1n, 0n, [])
      )
    case Con{Op.Drop{}, rest}:
      Ops.hunks(rest, k, 1n+d, ps)
    case Con{Op.Put{l}, rest}:
      Ops.hunks(rest, k, d, l <> ps)

# the hunks of a cut
def Cut.hunks(c: Cut) -> List<&2, Hunk>:
  match c:
    case Cut{s, o, n, e}:
      [Hunk{List.length(&2, Texts.Bytes(), s), List.length(&2, Texts.Bytes(), o), n}]

# the hunks of a cut c of a and b, applied to a, give b
def Lines.apply_cut_hunks(
  c: Cut,
  a: List<&2, Texts.Bytes()>,
  b: List<&2, Texts.Bytes()>,
  hl: {Cut.left(c) == a: List<&2, Texts.Bytes()>},
  hr: {Cut.right(c) == b: List<&2, Texts.Bytes()>}
) -> {Lines.apply.all(Cut.hunks(c), a) == b: List<&2, Texts.Bytes()>}:
  match c:
    case Cut{+s, +o, +n, +e}:
      length1 = List.length(&2, Texts.Bytes(), s)
      length2 = List.length(&2, Texts.Bytes(), o)
      %hl: {Lines.apply.all([Hunk{length1, length2, n}], _) == b: List<&2, Texts.Bytes()>}
      %hr:
        {
          Lines.apply.all([Hunk{length1, length2, n}], Cut.left(Cut{s, o, n, e}))
            == _: List<&2, Texts.Bytes()>
        }
      Equal.trans(
        List<&2, Texts.Bytes()>,
        Lines.apply.all([Hunk{length1, length2, n}], Cut.left(Cut{s, o, n, e})),
        Lines.apply(length1, Cut.left(Cut{s, o, n, e}), length2, n),
        Cut.right(Cut{s, o, n, e}),
        Lines.apply.all_one(length1, Cut.left(Cut{s, o, n, e}), length2, n),
        Lines.apply_cut(s, o, n, e)
      )

# the hunks m, when they make b of a; else the one cut of a and b
def Lines.diff.check(m: Maybe<&2, List<&2, Hunk>>, +a: List<&2, Texts.Bytes()>, +b: List<&2, Texts.Bytes()>) -> List<&2, Hunk>:
  match m:
    case Some{+hs}:
      Shared.Bool.when(
        List<&2, Hunk>,
        Shared.List.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), Lines.apply.all(hs, a), b),
        u => hs,
        u => Cut.hunks(Lines.cut(a, b))
      )
    case None{}:
      Cut.hunks(Lines.cut(a, b))

# the checked hunks, applied to a, give b
def Lines.diff.check_apply(
  m: Maybe<&2, List<&2, Hunk>>,
  +a: List<&2, Texts.Bytes()>,
  +b: List<&2, Texts.Bytes()>
) -> {Lines.apply.all(Lines.diff.check(m, a, b), a) == b: List<&2, Texts.Bytes()>}:
  match m:
    case Some{+hs}:
      Shared.Bool.when_cases(
        List<&2, Hunk>,
        r => {Lines.apply.all(r, a) == b: List<&2, Texts.Bytes()>},
        Shared.List.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), Lines.apply.all(hs, a), b),
        u => hs,
        u => Cut.hunks(Lines.cut(a, b)),
        e =>
          Shared.List.is_eq_sound(
            ~Texts.Bytes(),
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
            Lines.apply.all(hs, a),
            b
          )(e),
        e => Lines.apply_cut_hunks(Lines.cut(a, b), a, b, Lines.cut_left(a, b), Lines.cut_right(a, b))
      )
    case None{}:
      Lines.apply_cut_hunks(Lines.cut(a, b), a, b, Lines.cut_left(a, b), Lines.cut_right(a, b))

# the hunks from the lines a to the lines b, with the fewest lines dropped and
# put
def Lines.diff(+a: List<&2, Texts.Bytes()>, +b: List<&2, Texts.Bytes()>) -> List<&2, Hunk>:
  Lines.diff.check(
    Maybe.map(&2, List<&2, Op>, List<&2, Hunk>, ops => Ops.hunks(ops, 0n, 0n, []), Lines.ops(a, b)),
    a,
    b
  )

# the hunks of a diff of a and b, applied to a, give b
def Lines.apply_diff(
  +a: List<&2, Texts.Bytes()>,
  +b: List<&2, Texts.Bytes()>
) -> {Lines.apply.all(Lines.diff(a, b), a) == b: List<&2, Texts.Bytes()>}:
  Lines.diff.check_apply(
    Maybe.map(&2, List<&2, Op>, List<&2, Hunk>, ops => Ops.hunks(ops, 0n, 0n, []), Lines.ops(a, b)),
    a,
    b
  )

# Formats
# -------

# a change between two versions: Lines is hunks of lines; Whole is the new
# content; Pieces is the new shape of an embedding, with a patch for each of
# its texts and each of its regions
type Patch is Data:
  Patch.Lines{hunks: List<&2, Hunk>}
  Patch.Whole{bytes: Texts.Bytes()}
  Patch.Pieces{shape: List<&2, Shape>, texts: List<&2, Patch>, regions: List<&2, Patch>}

# x is not 0
def Plain.not_nul(x: U32) -> Bool:
  Bool.not(U32.is_eq(x, 0))

# b is text: no byte of it is 0
def Plain.is_text(b: Texts.Bytes()) -> Bool:
  List.all(~&2, ~U32, ~Plain.not_nul, b)

# the patch from a to b, as lines when both are text (text)
def Plain.diff.by(text: Bool, a: Texts.Bytes(), b: Texts.Bytes()) -> Patch:
  match text:
    case True{}:
      Patch.Lines{Lines.diff(Lines.list(a), Lines.list(b))}
    case False{}:
      Patch.Whole{b}

# the patch from a to b
def Plain.diff(+a: Texts.Bytes(), +b: Texts.Bytes()) -> Patch:
  Plain.diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# a after the patch p; a patch of an embedding leaves a as it is
def Plain.apply(a: Texts.Bytes(), p: Patch) -> Texts.Bytes():
  match p:
    case Patch.Lines{hs}:
      Lines.bytes(Lines.apply.all(hs, Lines.list(a)))
    case Patch.Whole{x}:
      x
    case Patch.Pieces{sh, ts, rs}:
      a

# Plain.apply_diff, by whether both are text (text)
def Plain.apply_diff.by(
  text: Bool,
  +a: Texts.Bytes(),
  +b: Texts.Bytes()
) -> {Plain.apply(a, Plain.diff.by(text, a, b)) == b: Texts.Bytes()}:
  match text:
    case True{}:
      +la = Lines.list(a)
      +lb = Lines.list(b)
      Equal.trans(
        Texts.Bytes(),
        Lines.bytes(Lines.apply.all(Lines.diff(la, lb), la)),
        Lines.bytes(lb),
        b,
        Equal.cong(
          List<&2, Texts.Bytes()>,
          Texts.Bytes(),
          z => Lines.bytes(z),
          Lines.apply.all(Lines.diff(la, lb), la),
          lb,
          Lines.apply_diff(la, lb)
        ),
        Lines.bytes_list(b)
      )
    case False{}:
      {==}

# the patch from a to b, applied to a, gives b
def Plain.apply_diff(
  +a: Texts.Bytes(),
  +b: Texts.Bytes()
) -> {Plain.apply(a, Plain.diff(a, b)) == b: Texts.Bytes()}:
  Plain.apply_diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# Merges
# ------
# A merge of x and y, two changes of b. Before any format looks, Merge.decide
# takes the one change when only one side changed, or when both made the same
# change; so these merges hold for every format (Format.merge_*). A format
# merges only what both sides changed, differently. Plain text merges by
# lines (diff3): a hunk of either side that ends before the other side's next
# hunk starts is taken.

# a merge: its bytes, or a clash
type Merged is Data:
  Merged.Clean{bytes: Texts.Bytes()}
  Merged.Clash{}

# a hunk where it is in its base: the lines from from to to are replaced by
# put
type Range is Data:
  Range{from: Nat, to: Nat, put: List<&2, Texts.Bytes()>}

# the ranges of the hunks hs, after the line at
def Hunks.ranges(hs: List<&2, Hunk>, +at: Nat) -> List<&2, Range>:
  match hs:
    case Nil{}:
      []
    case Con{Hunk{k, d, put}, rest}:
      +f = Nat.add(at, k)
      +t = Nat.add(f, d)
      Range{f, t, put} <> Hunks.ranges(rest, t)

# the hunks of the ranges rs, after the line at
def Ranges.hunks(rs: List<&2, Range>, +at: Nat) -> List<&2, Hunk>:
  match rs:
    case Nil{}:
      []
    case Con{Range{+f, +t, put}, rest}:
      Hunk{Nat.sub(f, at), Nat.sub(t, f), put} <> Ranges.hunks(rest, t)

# a and b are the same range
def Range.is_eq(a: Range, b: Range) -> Bool:
  match a b:
    case Range{f1, t1, p1} Range{f2, t2, p2}:
      Bool.and(
        Bool.and(Nat.is_eq(f1, f2), Nat.is_eq(t1, t2)),
        Shared.List.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), p1, p2)
      )

# the end of the range a comes before the start of b, with a line between
def Range.before(a: Range, b: Range) -> Bool:
  match a b:
    case Range{f1, t1, p1} Range{f2, t2, p2}:
      Nat.is_lt(t1, f2)

# the ranges of two changes of one base, in order: each where it is when it
# stands apart from the other side's, one when both made the same; none: two
# ranges meet and differ, a clash
def Ranges.merge(xs: List<&2, Range>, ys: List<&2, Range>) -> Maybe<&2, List<&2, Range>>:
  match xs ys:
    case Nil{} b:
      Some{b}
    case a Nil{}:
      Some{a}
    case Con{+x, +rx} Con{+y, +ry}:
      Shared.Bool.when(
        Maybe<&2, List<&2, Range>>,
        Range.before(x, y),
        u => Maybe.map(&2, List<&2, Range>, List<&2, Range>, m => x <> m, Ranges.merge(rx, Con{y, ry})),
        u => Shared.Bool.when(
          Maybe<&2, List<&2, Range>>,
          Range.before(y, x),
          w => Maybe.map(&2, List<&2, Range>, List<&2, Range>, m => y <> m, Ranges.merge(Con{x, rx}, ry)),
          w => Shared.Bool.when(
            Maybe<&2, List<&2, Range>>,
            Range.is_eq(x, y),
            v => Maybe.map(&2, List<&2, Range>, List<&2, Range>, m => x <> m, Ranges.merge(rx, ry)),
            v => None{}
          )
        )
      )

# the lines lb after the merged ranges m (none: a clash)
def Ranges.apply(m: Maybe<&2, List<&2, Range>>, lb: List<&2, Texts.Bytes()>) -> Merged:
  match m:
    case None{}:
      Merged.Clash{}
    case Some{rs}:
      Merged.Clean{Lines.bytes(Lines.apply.all(Ranges.hunks(rs, 0n), lb))}

# the merge of two text changes, by their lines: each hunk of either side
# that stands apart from the other side's hunks is taken (diff3)
def Plain.merge.lines(b: Texts.Bytes(), x: Texts.Bytes(), y: Texts.Bytes()) -> Merged:
  +lb = Lines.list(b)
  Ranges.apply(
    Ranges.merge(Hunks.ranges(Lines.diff(lb, Lines.list(x)), 0n), Hunks.ranges(Lines.diff(lb, Lines.list(y)), 0n)),
    lb
  )

# the merge of two different changes, as lines when all three are text (text)
def Plain.merge.text(text: Bool, b: Texts.Bytes(), x: Texts.Bytes(), y: Texts.Bytes()) -> Merged:
  match text:
    case True{}:
      Plain.merge.lines(b, x, y)
    case False{}:
      Merged.Clash{}

# what a merge takes: the side of a three-way choice (Sides.Side.of), or both
# changes piece by piece, when they are an embedding of one shape (pieces)
type Decision is Data:
  Decision.Side{side: Sides.Side}
  Decision.Pieces{}

# what a merge of x and y, two changes of b, takes before any format looks
def Merge.decide(b: Texts.Bytes(), x: Texts.Bytes(), y: Texts.Bytes()) -> Decision:
  Decision.Side{Sides.Side.of(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), b, x, y)}

# the change that the decision d takes of x and y, none for both
def Decision.take(d: Decision, x: Texts.Bytes(), y: Texts.Bytes()) -> Maybe<&2, Texts.Bytes()>:
  match d:
    case Decision.Side{s}:
      Sides.Side.take(Texts.Bytes(), s, x, y)
    case Decision.Pieces{}:
      None{}

# Embedding
# ---------
# An embedding holds regions of another format between an opening and a
# closing marker (a <script> in HTML, a fenced block in Markdown). Its content
# splits into pieces: the text between regions, and each region with or
# without its closing marker. The pieces join back into the same bytes, so a
# format inside another loses nothing.

# a piece of an embedding: text of the outer format, or a region of the inner
# one, closed by its marker or running to the end
type Piece is Data:
  Piece.Text{bytes: Texts.Bytes()}
  Piece.Region{bytes: Texts.Bytes(), closed: Bool}

# what kind a piece is, without its bytes
type Shape is Data:
  Shape.Text{}
  Shape.Region{closed: Bool}

# b starts with p
def Bytes.starts(p: Texts.Bytes(), b: Texts.Bytes()) -> Bool:
  match p b:
    case Nil{} w:
      True{}
    case Con{x, pr} Con{y, br}:
      List.all.if(u => Bytes.starts(pr, br), U32.is_eq(x, y))
    case Con{x, pr} Nil{}:
      False{}

# the place m of p in some bytes, after the byte x
def Bytes.find.put(
  x: U32,
  m: Maybe<&2, Texts.Cut<Texts.Bytes()>>
) -> Maybe<&2, Texts.Cut<Texts.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{Texts.Cut{u, w}}:
      Some{Texts.Cut{x <> u, w}}

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- List.length runs only at the hit, where the lazy search stops: once per search
# where p first occurs in b, if it does
def Bytes.find(+p: Texts.Bytes(), b: Texts.Bytes()) -> Maybe<&2, Texts.Cut<Texts.Bytes()>>:
  match b:
    case Nil{}:
      Bool.pick(
        Maybe<&2, Texts.Cut<Texts.Bytes()>>,
        List.is_empty(&2, U32, p),
        Some{Texts.Cut{[], []}},
        None{}
      )
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Texts.Cut<Texts.Bytes()>>,
        Bytes.starts(p, x <> r),
        u => Some{Texts.Cut{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
        u => Bytes.find.put(x, Bytes.find(p, r))
      )
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# the pieces of b, f steps at most: looking for an opening marker op (opening),
# or for the closing marker cl of a region (not opening); m is where the marker
# looked for first occurs in b
def Embed.split.go(
  f: Nat,
  +op: Texts.Bytes(),
  +cl: Texts.Bytes(),
  b: Texts.Bytes(),
  opening: Bool,
  m: Maybe<&2, Texts.Cut<Texts.Bytes()>>
) -> List<&2, Piece>:
  match f opening m:
    case 0n True{} w:
      [Piece.Text{b}]
    case 0n False{} w:
      [Piece.Region{b, False{}}]
    case 1n+e True{} None{}:
      [Piece.Text{b}]
    case 1n+e True{} Some{Texts.Cut{u, +w}}:
      Piece.Text{u} <> Embed.split.go(e, op, cl, w, False{}, Bytes.find(cl, w))
    case 1n+e False{} None{}:
      [Piece.Region{b, False{}}]
    case 1n+e False{} Some{Texts.Cut{u, +w}}:
      Piece.Region{u, True{}} <> Embed.split.go(e, op, cl, w, True{}, Bytes.find(op, w))

# the pieces of b, between the markers op and cl
def Embed.split(+op: Texts.Bytes(), cl: Texts.Bytes(), +b: Texts.Bytes()) -> List<&2, Piece>:
  Embed.split.go(1n+List.length(&2, U32, b), op, cl, b, True{}, Bytes.find(op, b))

# the bytes of the pieces ps, with the markers op and cl around each region
def Embed.join(+op: Texts.Bytes(), +cl: Texts.Bytes(), ps: List<&2, Piece>) -> Texts.Bytes():
  match ps:
    case Nil{}:
      []
    case Con{Piece.Text{t}, r}:
      List.append(&2, U32, t, Embed.join(op, cl, r))
    case Con{Piece.Region{c, True{}}, r}:
      List.append(
        &2,
        U32,
        op,
        List.append(&2, U32, c, List.append(&2, U32, cl, Embed.join(op, cl, r)))
      )
    case Con{Piece.Region{c, False{}}, r}:
      List.append(&2, U32, op, List.append(&2, U32, c, Embed.join(op, cl, r)))

# the bytes before a found place
def Bytes.find.before(m: Maybe<&2, Texts.Cut<Texts.Bytes()>>) -> Texts.Bytes():
  match m:
    case Some{Texts.Cut{u, w}}:
      u
    case None{}:
      []

# the bytes after a found place
def Bytes.find.after(m: Maybe<&2, Texts.Cut<Texts.Bytes()>>) -> Texts.Bytes():
  match m:
    case Some{Texts.Cut{u, w}}:
      w
    case None{}:
      []

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bytes that start with p are p, then the rest
def Bytes.starts_drop(
  p: Texts.Bytes(),
  b: Texts.Bytes()
) -> {
  Bytes.starts(p, b) == True{}: Bool
} -> {b == List.append(&2, U32, p, List.drop(&2, U32, b, List.length(&2, U32, p))): Texts.Bytes()}:
  match p b:
    case Nil{} w:
      h => Equal.sym(Texts.Bytes(), List.drop(&2, U32, w, 0n), w, Shared.List.drop_zero(&2, U32, w))
    case Con{+x, +pr} Con{+y, +br}:
      +h =>
        %Equal.sym(
          U32,
          x,
          y,
          Shared.U32.is_eq_sound(
            x,
            y
          )(Shared.List.all.if_hit(U32.is_eq(x, y), u => Bytes.starts(pr, br))(h))
        ):
          {
            y
              <> br
              == _
              <> List.append(
                &2,
                U32,
                pr,
                List.drop(&2, U32, br, List.length(&2, U32, pr))
              ): Texts.Bytes()
          }
        %Bytes.starts_drop(
          pr,
          br
        )(Shared.List.all.if_rest(U32.is_eq(x, y), u => Bytes.starts(pr, br))(h)):
          {y <> br == y <> _: Texts.Bytes()}
        {==}
    case Con{x, pr} Nil{}:
      h => Empty.absurd(
        {
          Nil{}
            == List.append(
              &2,
              U32,
              x <> pr,
              List.drop(&2, U32, Nil{}, List.length(&2, U32, x <> pr))
            ): Texts.Bytes()
        },
        Shared.Bool.false_ne_true(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Bytes.find_cut at x <> r, by whether p starts there (hit)
def Bytes.find_cut.at(
  -u: Texts.Bytes(),
  -w: Texts.Bytes(),
  hit: Bool,
  +p: Texts.Bytes(),
  +x: U32,
  +r: Texts.Bytes(),
  rest: Maybe<&2, Texts.Cut<Texts.Bytes()>>,
  eh: {Bytes.starts(p, x <> r) == hit: Bool},
  ih: @u2: Texts.Bytes() -> @w2: Texts.Bytes() -> {
    rest == Some{Texts.Cut{u2, w2}}: Maybe<&2, Texts.Cut<Texts.Bytes()>>
  } -> {r == List.append(&2, U32, u2, List.append(&2, U32, p, w2)): Texts.Bytes()}
) -> {
  Shared.Bool.when(
    Maybe<&2, Texts.Cut<Texts.Bytes()>>,
    hit,
    z => Some{Texts.Cut{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
    z => Bytes.find.put(x, rest)
  )
    == Some{Texts.Cut{u, w}}: Maybe<&2, Texts.Cut<Texts.Bytes()>>
} -> {x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Texts.Bytes()}:
  match hit rest:
    case True{} m:
      +h =>
        +drop1 = List.drop(&2, U32, x <> r, List.length(&2, U32, p))
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.before(z),
          Some{Texts.Cut{[], drop1}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Texts.Bytes()}
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.after(z),
          Some{Texts.Cut{[], drop1}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, p, _): Texts.Bytes()}
        Bytes.starts_drop(p, x <> r)(eh)
    case False{} None{}:
      h => Empty.absurd(
        {x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Texts.Bytes()},
        Shared.Maybe.none_ne_some(Texts.Cut<Texts.Bytes()>, Texts.Cut{u, w}, h)
      )
    case False{} Some{Texts.Cut{u2, w2}}:
      +h =>
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.before(z),
          Some{Texts.Cut{x <> u2, w2}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Texts.Bytes()}
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.after(z),
          Some{Texts.Cut{x <> u2, w2}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {x <> r == x <> List.append(&2, U32, u2, List.append(&2, U32, p, _)): Texts.Bytes()}
        %ih(u2)(w2)({==}): {x <> r == x <> _: Texts.Bytes()}
        {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# what Bytes.find finds cuts b: the bytes before, the pattern, the bytes after
def Bytes.find_cut(
  -u: Texts.Bytes(),
  -w: Texts.Bytes(),
  b: Texts.Bytes(),
  +p: Texts.Bytes()
) -> {
  Bytes.find(p, b) == Some{Texts.Cut{u, w}}: Maybe<&2, Texts.Cut<Texts.Bytes()>>
} -> {b == List.append(&2, U32, u, List.append(&2, U32, p, w)): Texts.Bytes()}:
  match b p:
    case Nil{} Nil{}:
      +h =>
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.before(z),
          Some{Texts.Cut{[], []}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {Nil{} == List.append(&2, U32, _, List.append(&2, U32, Nil{}, w)): Texts.Bytes()}
        %Equal.cong(
          Maybe<&2, Texts.Cut<Texts.Bytes()>>,
          Texts.Bytes(),
          z => Bytes.find.after(z),
          Some{Texts.Cut{[], []}},
          Some{Texts.Cut{u, w}},
          h
        ):
          {Nil{} == List.append(&2, U32, Nil{}, List.append(&2, U32, Nil{}, _)): Texts.Bytes()}
        {==}
    case Nil{} Con{y, q}:
      h => Empty.absurd(
        {Nil{} == List.append(&2, U32, u, List.append(&2, U32, y <> q, w)): Texts.Bytes()},
        Shared.Maybe.none_ne_some(Texts.Cut<Texts.Bytes()>, Texts.Cut{u, w}, h)
      )
    case Con{+x, +r} m:
      Bytes.find_cut.at(
        u,
        w,
        Bytes.starts(m, x <> r),
        m,
        x,
        r,
        Bytes.find(m, r),
        {==},
        u2 => w2 => e => Bytes.find_cut(u2, w2, r, m)(e)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the marker that a split looks for: op outside a region (opening), cl inside
def Embed.marker(opening: Bool, op: Texts.Bytes(), cl: Texts.Bytes()) -> Texts.Bytes():
  match opening:
    case True{}:
      op
    case False{}:
      cl

# the bytes that the pieces of a split stand for: b outside a region
# (opening), else the opening marker op, then b
def Embed.whole(opening: Bool, op: Texts.Bytes(), b: Texts.Bytes()) -> Texts.Bytes():
  match opening:
    case True{}:
      b
    case False{}:
      List.append(&2, U32, op, b)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the pieces of a split, joined, give back what they stand for
def Embed.join_split.go(
  f: Nat,
  +op: Texts.Bytes(),
  +cl: Texts.Bytes(),
  b: Texts.Bytes(),
  opening: Bool,
  m: Maybe<&2, Texts.Cut<Texts.Bytes()>>,
  hm: @u: Texts.Bytes() -> @w: Texts.Bytes() -> {
    m == Some{Texts.Cut{u, w}}: Maybe<&2, Texts.Cut<Texts.Bytes()>>
  } -> {
    b
      == List.append(
        &2,
        U32,
        u,
        List.append(&2, U32, Embed.marker(opening, op, cl), w)
      ): Texts.Bytes()
  }
) -> {
  Embed.join(
    op,
    cl,
    Embed.split.go(f, op, cl, b, opening, m)
  )
    == Embed.whole(opening, op, b): Texts.Bytes()
}:
  match f opening m:
    case 0n True{} n:
      Shared.List.append_nil(U32, b)
    case 0n False{} n:
      Equal.cong(
        Texts.Bytes(),
        Texts.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, b, []),
        b,
        Shared.List.append_nil(U32, b)
      )
    case 1n+e True{} None{}:
      Shared.List.append_nil(U32, b)
    case 1n+e True{} Some{Texts.Cut{u, +w}}:
      append1 = List.append(&2, U32, op, w)
      %Equal.sym(
        Texts.Bytes(),
        Embed.join(op, cl, Embed.split.go(e, op, cl, w, False{}, Bytes.find(cl, w))),
        append1,
        Embed.join_split.go(
          e,
          op,
          cl,
          w,
          False{},
          Bytes.find(cl, w),
          u2 => w2 => h => Bytes.find_cut(u2, w2, w, cl)(h)
        )
      ):
        {List.append(&2, U32, u, _) == b: Texts.Bytes()}
      Equal.sym(Texts.Bytes(), b, List.append(&2, U32, u, append1), hm(u)(w)({==}))
    case 1n+e False{} None{}:
      Equal.cong(
        Texts.Bytes(),
        Texts.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, b, []),
        b,
        Shared.List.append_nil(U32, b)
      )
    case 1n+e False{} Some{Texts.Cut{+u, +w}}:
      append1 = List.append(&2, U32, u, List.append(&2, U32, cl, w))
      %Equal.sym(
        Texts.Bytes(),
        Embed.join(op, cl, Embed.split.go(e, op, cl, w, True{}, Bytes.find(op, w))),
        w,
        Embed.join_split.go(
          e,
          op,
          cl,
          w,
          True{},
          Bytes.find(op, w),
          u2 => w2 => h => Bytes.find_cut(u2, w2, w, op)(h)
        )
      ):
        {
          List.append(
            &2,
            U32,
            op,
            List.append(&2, U32, u, List.append(&2, U32, cl, _))
          )
            == List.append(&2, U32, op, b): Texts.Bytes()
        }
      Equal.cong(
        Texts.Bytes(),
        Texts.Bytes(),
        z => List.append(&2, U32, op, z),
        append1,
        b,
        Equal.sym(Texts.Bytes(), b, append1, hm(u)(w)({==}))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the pieces of b, joined, give back b: an embedding loses nothing
def Embed.join_split(
  +op: Texts.Bytes(),
  cl: Texts.Bytes(),
  +b: Texts.Bytes()
) -> {Embed.join(op, cl, Embed.split(op, cl, b)) == b: Texts.Bytes()}:
  Embed.join_split.go(
    1n+List.length(&2, U32, b),
    op,
    cl,
    b,
    True{},
    Bytes.find(op, b),
    u => w => h => Bytes.find_cut(u, w, b, op)(h)
  )

# the shape of a piece
def Piece.shape(p: Piece) -> Shape:
  match p:
    case Piece.Text{t}:
      Shape.Text{}
    case Piece.Region{c, k}:
      Shape.Region{k}

# the shapes of the pieces ps
def Pieces.shape(ps: List<&2, Piece>) -> List<&2, Shape>:
  match ps:
    case Nil{}:
      []
    case Con{p, r}:
      Piece.shape(p) <> Pieces.shape(r)

# the bytes of the text pieces of ps, in order
def Pieces.texts(ps: List<&2, Piece>) -> List<&2, Texts.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.Text{t}, r}:
      t <> Pieces.texts(r)
    case Con{Piece.Region{c, k}, r}:
      Pieces.texts(r)

# the bytes of the regions of ps, in order
def Pieces.regions(ps: List<&2, Piece>) -> List<&2, Texts.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.Text{t}, r}:
      Pieces.regions(r)
    case Con{Piece.Region{c, k}, r}:
      c <> Pieces.regions(r)

# the pieces of the shapes sh, filled with the texts ts and the regions rs in
# order; a missing one is empty
def Pieces.build(
  sh: List<&2, Shape>,
  ts: List<&2, Texts.Bytes()>,
  rs: List<&2, Texts.Bytes()>
) -> List<&2, Piece>:
  match sh ts rs:
    case Nil{} t r:
      []
    case Con{Shape.Text{}, sr} Nil{} r:
      Piece.Text{[]} <> Pieces.build(sr, [], r)
    case Con{Shape.Text{}, sr} Con{t, tr} r:
      Piece.Text{t} <> Pieces.build(sr, tr, r)
    case Con{Shape.Region{k}, sr} t Nil{}:
      Piece.Region{[], k} <> Pieces.build(sr, t, [])
    case Con{Shape.Region{k}, sr} t Con{c, rr}:
      Piece.Region{c, k} <> Pieces.build(sr, t, rr)

# the pieces of their own shape, texts and regions are the pieces
def Pieces.build_of(
  ps: List<&2, Piece>
) -> {Pieces.build(Pieces.shape(ps), Pieces.texts(ps), Pieces.regions(ps)) == ps: List<&2, Piece>}:
  match ps:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Piece.Text{bytes}:
          %Equal.sym(
            List<&2, Piece>,
            Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)),
            tail,
            Pieces.build_of(tail)
          ):
            {Piece.Text{bytes} <> _ == Piece.Text{bytes} <> tail: List<&2, Piece>}
          {==}
        case Piece.Region{bytes1, closed}:
          %Equal.sym(
            List<&2, Piece>,
            Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)),
            tail,
            Pieces.build_of(tail)
          ):
            {
              Piece.Region{
                bytes1,
                closed
              }
                <> _
                == Piece.Region{bytes1, closed}
                <> tail: List<&2, Piece>
            }
          {==}

# Changes
# -------
# What a patch does, part by part, for a reader.

# a part of a resource: its kind (line, content, or what a format names, like
# a function), its name (empty: it has none), where it is (a line counts from
# 1; a whole content is at 0), its bytes, and the names of the items that it
# uses
type Item is Data:
  Item{
    kind: String,
    name: Texts.Bytes(),
    place: Nat,
    bytes: Texts.Bytes(),
    uses: List<&2, Texts.Bytes()>
  }

# a part that a patch added or removed
type Change is Data:
  Change.Added{item: Item}
  Change.Removed{item: Item}

# the lines ls as the changes that make (c), counted from the line at
def Lines.changes(~make: Item -> Change, ls: List<&2, Texts.Bytes()>, +at: Nat) -> List<&2, Change>:
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      make(Item{"line", [], at, l, []}) <> Lines.changes(~make, r, 1n+at)

# the changes of a whole content from a to b, none when they are the same
# (held)
def Plain.changes.whole(held: Bool, a: Texts.Bytes(), b: Texts.Bytes()) -> List<&2, Change>:
  match held:
    case True{}:
      []
    case False{}:
      [Change.Removed{Item{"content", [], 0n, a, []}}, Change.Added{Item{"content", [], 0n, b, []}}]

# the changes of the hunks hs of the old lines ls, the first of which is the
# line at
def Hunks.changes(hs: List<&2, Hunk>, +ls: List<&2, Texts.Bytes()>, +at: Nat) -> List<&2, Change>:
  match hs:
    case Nil{}:
      []
    case Con{Hunk{+k, +d, put}, rest}:
      +p = Nat.add(at, k)
      List.append(
        &2,
        Change,
        Lines.changes(~(i => Change.Removed{i}), List.take(&2, Texts.Bytes(), List.drop(&2, Texts.Bytes(), ls, k), d), 1n+p),
        List.append(
          &2,
          Change,
          Lines.changes(~(i => Change.Added{i}), put, 1n+p),
          Hunks.changes(rest, List.drop(&2, Texts.Bytes(), ls, Nat.add(k, d)), Nat.add(p, d))
        )
      )

# the changes of the patch p of a
def Plain.changes.of(+a: Texts.Bytes(), p: Patch) -> List<&2, Change>:
  match p:
    case Patch.Lines{hs}:
      Hunks.changes(hs, Lines.list(a), 0n)
    case Patch.Whole{+x}:
      Plain.changes.whole(Shared.List.is_eq(~U32, ~U32.is_eq, a, x), a, x)
    case Patch.Pieces{sh, ts, rs}:
      []

# what changed from a to b, part by part
def Plain.changes(+a: Texts.Bytes(), b: Texts.Bytes()) -> List<&2, Change>:
  Plain.changes.of(a, Plain.diff(a, b))

# Imports
# -------
# A language names what a resource uses on lines of its own: an import, an
# include. Its rule says how to read those lines, and the conditions that each
# one sits under, so a conditional import is an edge with its conditions, and a
# qualified one keeps its alias.

# what an import brings into scope, beyond what it names: only the names
# that it asks for; all of its target; or all of its target and all that the
# target brings, at any depth (an include, a re-export)
type Brings is Data:
  Brings.Named{}
  Brings.Whole{}
  Brings.Through{}

# how a language finds the target of an import: sep, in the target as
# written, stands for a step down a path (none: the target is a path); local:
# the language looks first beside the resource that imports; then under each
# of roots; each with each of suffixes (a suffix may be empty)
type Find is Data:
  Find{sep: Maybe<&2, Char>, local: Bool, roots: List<&2, String>, suffixes: List<&2, String>}

# a line that starts with start, after blanks, names a target after the
# marker open, up to the marker close or the line's end, and after the marker
# alias the name that it gets; a line that starts with when opens a
# condition, otherwise flips it, end closes it. An empty marker never starts a
# line; an empty open or close is the place right after start or the line's
# end. Such an import brings what brings says, and its target is found as
# find says.
type Rule is Data:
  Rule{
    start: Texts.Bytes(),
    open: Texts.Bytes(),
    close: Texts.Bytes(),
    alias: Texts.Bytes(),
    when: Texts.Bytes(),
    otherwise: Texts.Bytes(),
    end: Texts.Bytes(),
    brings: Brings,
    find: Find
  }

# a condition that an edge sits under: its line, and whether the edge is in
# its first part (holds) or after otherwise
type Cond is Data:
  Cond{test: Texts.Bytes(), holds: Bool}

# what the view vs sets the test x to, if it names it: a view is the
# conditions that one build sets, each test with whether it holds
def View.get(vs: List<&2, Cond>, +x: Texts.Bytes()) -> Maybe<&2, Bool>:
  match vs:
    case Nil{}:
      None{}
    case Con{Cond{y, h}, rest}:
      Shared.Bool.when(
        Maybe<&2, Bool>,
        Shared.List.is_eq(~U32, ~U32.is_eq, y, x),
        u => Some{h},
        u => View.get(rest, x)
      )

# the condition c holds under the view vs. A test that the view does not name
# holds: what a build may set counts, so no use is missed
def Cond.holds(vs: List<&2, Cond>, c: Cond) -> Bool:
  match c:
    case Cond{x, h}:
      Maybe.default(
        &2,
        Bool,
        Maybe.bind(&2, Bool, Bool, View.get(vs, x), v => Some{Shared.Bool.is_eq(v, h)}),
        True{}
      )

# each of the conditions cs holds under the view vs
def Conds.hold(+vs: List<&2, Cond>, cs: List<&2, Cond>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      List.all.if(u => Conds.hold(vs, rest), Cond.holds(vs, c))

# what an import asks for, as written: its target, the name that it gets
# (empty without one), the names of the items of the target that it asks for
# (none: it names none), and the conditions that it sits under, innermost
# first
type Edge is Data:
  Edge{
    target: Texts.Bytes(),
    alias: Texts.Bytes(),
    names: List<&2, Texts.Bytes()>,
    conds: List<&2, Cond>
  }

# an import: what it asks for, kept as written; what it brings, which may be
# more; and how its target is found
type Import is Data:
  Import{asked: Edge, brings: Brings, find: Find}

# the import x is in the build of the view vs: each condition that it sits
# under holds
def Import.holds(vs: List<&2, Cond>, x: Import) -> Bool:
  match x:
    case Import{Edge{t, al, ns, cs}, br, fi}:
      Conds.hold(vs, cs)

# x is a space or a tab
def Line.is_blank(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9))

# l without its leading blanks
def Line.trim(l: Texts.Bytes()) -> Texts.Bytes():
  match l:
    case Nil{}:
      []
    case Con{+x, +r}:
      Shared.Bool.when(Texts.Bytes(), Line.is_blank(x), u => Line.trim(r), u => x <> r)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- Bytes.starts of an empty marker returns at once
# l starts with the marker p, which is not empty
def Line.marks(+p: Texts.Bytes(), l: Texts.Bytes()) -> Bool:
  Bool.and(Bool.not(List.is_empty(&2, U32, p)), Bytes.starts(p, l))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# x cut where the marker m was found, when it is not empty (held): all of x
# comes before it when it is empty or not in x
def Rule.cut.of(
  held: Bool,
  m: Maybe<&2, Texts.Cut<Texts.Bytes()>>,
  x: Texts.Bytes()
) -> Texts.Cut<Texts.Bytes()>:
  match held m:
    case True{} Some{f}:
      f
    case h n:
      Texts.Cut{x, []}

# x cut at the first marker p
def Rule.cut(+p: Texts.Bytes(), +x: Texts.Bytes()) -> Texts.Cut<Texts.Bytes()>:
  Rule.cut.of(Bool.not(List.is_empty(&2, U32, p)), Bytes.find(p, x), x)

# the edge whose target and what follows it are cut at the close marker (c),
# with the alias marker al, under the conditions cs
def Rule.named(c: Texts.Cut<Texts.Bytes()>, al: Texts.Bytes(), cs: List<&2, Cond>) -> Edge:
  match c:
    case Texts.Cut{t, w}:
      Edge{t, Texts.Cut.after(Texts.Bytes(), Rule.cut(al, w)), [], cs}

# the edges of the bytes w after a start marker, once the open marker is
# known to be empty or not (held), and m is where it first occurs in w
def Rule.opened(
  held: Bool,
  m: Maybe<&2, Texts.Cut<Texts.Bytes()>>,
  w: Texts.Bytes(),
  cl: Texts.Bytes(),
  al: Texts.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match held m:
    case False{} n:
      [Rule.named(Rule.cut(cl, w), al, cs)]
    case True{} None{}:
      []
    case True{} Some{Texts.Cut{u, a}}:
      [Rule.named(Rule.cut(cl, a), al, cs)]

# the edges of the trimmed line t, once it is known to start with the start
# marker st or not (started)
def Rule.line.at(
  started: Bool,
  st: Texts.Bytes(),
  t: Texts.Bytes(),
  +op: Texts.Bytes(),
  cl: Texts.Bytes(),
  al: Texts.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match started:
    case True{}:
      +w = List.drop(&2, U32, t, List.length(&2, U32, st))
      Rule.opened(Bool.not(List.is_empty(&2, U32, op)), Bytes.find(op, w), w, cl, al, cs)
    case False{}:
      []

# the edges that the line l names under the conditions cs: one or none
def Rule.line(r: Rule, l: Texts.Bytes(), cs: List<&2, Cond>) -> List<&2, Edge>:
  match r:
    case Rule{+st, op, cl, al, wh, ot, en, br, fi}:
      +t = Line.trim(l)
      Rule.line.at(Line.marks(st, t), st, t, op, cl, al, cs)

# the conditions cs with the innermost one flipped
def Cond.flip(cs: List<&2, Cond>) -> List<&2, Cond>:
  match cs:
    case Nil{}:
      []
    case Con{Cond{x, h}, r}:
      Cond{x, Bool.not(h)} <> r

# the conditions after the trimmed line t, once it is known to close one
# (closes), flip one (flips) or open one (opens)
def Rule.step.at(
  closes: Bool,
  flips: Bool,
  opens: Bool,
  t: Texts.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Cond>:
  match closes flips opens:
    case True{} f o:
      List.tail(&2, Cond, cs)
    case False{} True{} o:
      Cond.flip(cs)
    case False{} False{} True{}:
      Cond{t, True{}} <> cs
    case False{} False{} False{}:
      cs

# the conditions cs after the line l
def Rule.step(r: Rule, l: Texts.Bytes(), cs: List<&2, Cond>) -> List<&2, Cond>:
  match r:
    case Rule{st, op, cl, al, wh, ot, en, br, fi}:
      +t = Line.trim(l)
      Rule.step.at(Line.marks(en, t), Line.marks(ot, t), Line.marks(wh, t), t, cs)

# the edges of the lines ls under the conditions cs
def Rule.edges.go(ls: List<&2, Texts.Bytes()>, +r: Rule, +cs: List<&2, Cond>) -> List<&2, Edge>:
  match ls:
    case Nil{}:
      []
    case Con{+l, rest}:
      List.append(&2, Edge, Rule.line(r, l, cs), Rule.edges.go(rest, r, Rule.step(r, l, cs)))

# the edges of the bytes b
def Rule.edges(r: Rule, b: Texts.Bytes()) -> List<&2, Edge>:
  Rule.edges.go(Lines.list(b), r, [])

# the imports of the edges es, which bring br and are found by fi
def Rule.imports(es: List<&2, Edge>, +br: Brings, +fi: Find) -> List<&2, Import>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      Import{e, br, fi} <> Rule.imports(rest, br, fi)

# the imports of the bytes b, by the rule r
def Rule.imports.of(+r: Rule, b: Texts.Bytes()) -> List<&2, Import>:
  match r:
    case Rule{st, op, cl, al, wh, ot, en, br, fi}:
      Rule.imports(Rule.edges(Rule{st, op, cl, al, wh, ot, en, br, fi}, b), br, fi)

# Nested formats
# --------------
# A format is a leaf, an embedding of an inner format in an outer one, or a
# language: a base format, the rule of its imports, and the imports that it
# makes with no line (a prelude, the other resources of a package). Formats
# nest to any depth (CSS and JS inside HTML), and the laws below hold for
# every one. A language with more rules is a language whose base is one. Each
# operation takes a list of items, so that an embedding hands all its texts to
# the outer format and all its regions to the inner one in one call; an old
# item that is missing is empty.
type Format is Data:
  Format.Leaf{kind: Leaf}
  Format.Embed{outer: Format, open: Texts.Bytes(), close: Texts.Bytes(), inner: Format}
  Format.Code{base: Format, rule: Rule, implicit: List<&2, Import>}

# a format that holds no other: lines (the default), the content as one whole
# part, or a submodule, a pointer to a child that the core reads and merges
type Leaf is Data:
  Leaf.Lines{}
  Leaf.Whole{}
  Leaf.Module{}

# the first of the items xs, empty when there is none
def Items.first(xs: List<&2, Texts.Bytes()>) -> Texts.Bytes():
  Maybe.default(&2, Texts.Bytes(), List.head(&2, Texts.Bytes(), xs), [])

# the patch from a to b, in the leaf k
def Leaf.diff(k: Leaf, a: Texts.Bytes(), b: Texts.Bytes()) -> Patch:
  match k:
    case Leaf.Lines{}:
      Plain.diff(a, b)
    case Leaf.Whole{}:
      Patch.Whole{b}
    case Leaf.Module{}:
      Patch.Whole{b}

# the patch from a to b, in the leaf k, applied to a, gives b
def Leaf.apply_diff(
  k: Leaf,
  a: Texts.Bytes(),
  b: Texts.Bytes()
) -> {Plain.apply(a, Leaf.diff(k, a, b)) == b: Texts.Bytes()}:
  match k:
    case Leaf.Lines{}:
      Plain.apply_diff(a, b)
    case Leaf.Whole{}:
      {==}
    case Leaf.Module{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the patches from the items as to the items bs, one for each of bs
def Format.diffs(
  f: Format,
  bs: List<&2, Texts.Bytes()>,
  +as: List<&2, Texts.Bytes()>
) -> List<&2, Patch>:
  match f bs:
    case Format.Leaf{k} Nil{}:
      []
    case Format.Leaf{+k} Con{b, br}:
      Leaf.diff(
        k,
        Items.first(as),
        b
      )
        <> Format.diffs(Format.Leaf{k}, br, List.tail(&2, Texts.Bytes(), as))
    case Format.Embed{o, op, cl, i} Nil{}:
      []
    case Format.Embed{+o, +op, +cl, +i} Con{b, br}:
      +pa = Embed.split(op, cl, Items.first(as))
      +pb = Embed.split(op, cl, b)
      tb = Pieces.texts(pb)
      ta = Pieces.texts(pa)
      rb = Pieces.regions(pb)
      ra = Pieces.regions(pa)
      ts rs rest = Format.diffs(
        o,
        tb,
        ta
      ) Format.diffs(
        i,
        rb,
        ra
      ) Format.diffs(Format.Embed{o, op, cl, i}, br, List.tail(&2, Texts.Bytes(), as))
      Patch.Pieces{Pieces.shape(pb), ts, rs} <> rest
    case Format.Code{base, r, im} c:
      Format.diffs(base, c, as)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the items as after the patches ps, one for each of ps; a patch of another
# format applies as plain
def Format.applies(
  f: Format,
  ps: List<&2, Patch>,
  +as: List<&2, Texts.Bytes()>
) -> List<&2, Texts.Bytes()>:
  match f ps:
    case Format.Leaf{k} Nil{}:
      []
    case Format.Leaf{+k} Con{p, pr}:
      Plain.apply(
        Items.first(as),
        p
      )
        <> Format.applies(Format.Leaf{k}, pr, List.tail(&2, Texts.Bytes(), as))
    case Format.Embed{o, op, cl, i} Nil{}:
      []
    case Format.Embed{+o, +op, +cl, +i} Con{Patch.Pieces{sh, tps, rps}, pr}:
      +pa = Embed.split(op, cl, Items.first(as))
      ta = Pieces.texts(pa)
      ra = Pieces.regions(pa)
      ts rs rest = Format.applies(
        o,
        tps,
        ta
      ) Format.applies(
        i,
        rps,
        ra
      ) Format.applies(Format.Embed{o, op, cl, i}, pr, List.tail(&2, Texts.Bytes(), as))
      Embed.join(op, cl, Pieces.build(sh, ts, rs)) <> rest
    case Format.Embed{+o, +op, +cl, +i} Con{p, pr}:
      Plain.apply(
        Items.first(as),
        p
      )
        <> Format.applies(Format.Embed{o, op, cl, i}, pr, List.tail(&2, Texts.Bytes(), as))
    case Format.Code{base, r, im} q:
      Format.applies(base, q, as)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# the patches from as to bs, applied to as, give bs, in every format
law Format.apply_diffs:
  for f: Format
  for +bs: List<&2, Texts.Bytes()>
  for +as: List<&2, Texts.Bytes()>
  {Format.applies(f, Format.diffs(f, bs, as), as) == bs: List<&2, Texts.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Format.apply_diffs(f, bs, as):
  match f bs:
    case Format.Leaf{k} Nil{}:
      {==}
    case Format.Leaf{+k} Con{b, br}:
      tail1 = List.tail(&2, Texts.Bytes(), as)
      Shared.List.cons_eq(
        Texts.Bytes(),
        Plain.apply(Items.first(as), Leaf.diff(k, Items.first(as), b)),
        b,
        Format.applies(Format.Leaf{k}, Format.diffs(Format.Leaf{k}, br, tail1), tail1),
        br,
        Leaf.apply_diff(k, Items.first(as), b),
        Format.apply_diffs(Format.Leaf{k}, br, tail1)
      )
    case Format.Embed{o, op, cl, i} Nil{}:
      {==}
    case Format.Embed{+o, +op, +cl, +i} Con{+b, br}:
      +pa = Embed.split(op, cl, Items.first(as))
      +pb = Embed.split(op, cl, b)
      ta = Pieces.texts(pa)
      ra = Pieces.regions(pa)
      tb = Pieces.texts(pb)
      rb = Pieces.regions(pb)
      rest = List.tail(&2, Texts.Bytes(), as)
      Shared.List.cons_eq(
        Texts.Bytes(),
        Embed.join(op, cl, Pieces.build(Pieces.shape(pb), Format.applies(o, Format.diffs(o, tb, ta), ta), Format.applies(i, Format.diffs(i, rb, ra), ra))),
        b,
        Format.applies(Format.Embed{o, op, cl, i}, Format.diffs(Format.Embed{o, op, cl, i}, br, rest), rest),
        br,
        %Equal.sym(List<&2, Texts.Bytes()>, Format.applies(o, Format.diffs(o, tb, ta), ta), tb, Format.apply_diffs(o, tb, ta)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), _, Format.applies(i, Format.diffs(i, rb, ra), ra))) == b: Texts.Bytes()}
        %Equal.sym(List<&2, Texts.Bytes()>, Format.applies(i, Format.diffs(i, rb, ra), ra), rb, Format.apply_diffs(i, rb, ra)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), tb, _)) == b: Texts.Bytes()}
        %Equal.sym(List<&2, Piece>, Pieces.build(Pieces.shape(pb), tb, rb), pb, Pieces.build_of(pb)):
          {Embed.join(op, cl, _) == b: Texts.Bytes()}
        Embed.join_split(op, cl, b),
        Format.apply_diffs(Format.Embed{o, op, cl, i}, br, rest))
    case Format.Code{base, r, im} c:
      Format.apply_diffs(base, c, as)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Nested merges
# -------------

# a and b are the same kind of piece
def Shape.is_eq(a: Shape, b: Shape) -> Bool:
  match a b:
    case Shape.Text{} Shape.Text{}:
      True{}
    case Shape.Region{True{}} Shape.Region{True{}}:
      True{}
    case Shape.Region{False{}} Shape.Region{False{}}:
      True{}
    case _ _:
      False{}

# the shape of the pieces of b, between the markers op and cl
def Embed.shape(op: Texts.Bytes(), cl: Texts.Bytes(), b: Texts.Bytes()) -> List<&2, Shape>:
  Pieces.shape(Embed.split(op, cl, b))

# what to take when both changes differ, in the format f
def Format.decide.both(f: Format, b: Texts.Bytes(), x: Texts.Bytes(), y: Texts.Bytes()) -> Decision:
  match f:
    case Format.Leaf{k}:
      Decision.Side{Sides.Side.Both{}}
    case Format.Embed{o, +op, +cl, i}:
      +sb = Embed.shape(op, cl, b)
      Bool.pick(
        Decision,
        List.all.if(
          u => Shared.List.is_eq(~Shape, ~Shape.is_eq, sb, Embed.shape(op, cl, y)),
          Shared.List.is_eq(~Shape, ~Shape.is_eq, sb, Embed.shape(op, cl, x))
        ),
        Decision.Pieces{},
        Decision.Side{Sides.Side.Both{}}
      )
    case Format.Code{base, r, im}:
      Format.decide.both(base, b, x, y)

# the decision d, in the format f
def Format.decide.on(
  d: Decision,
  f: Format,
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Decision:
  match d:
    case Decision.Side{Sides.Side.Both{}}:
      Format.decide.both(f, b, x, y)
    case e:
      e

# what a merge of x and y, two changes of b, takes in the format f
def Format.decide(f: Format, +b: Texts.Bytes(), +x: Texts.Bytes(), +y: Texts.Bytes()) -> Decision:
  Format.decide.on(Merge.decide(b, x, y), f, b, x, y)

# a merge to make: the base, the two changes, and what to take
type Job is Data:
  Job{base: Texts.Bytes(), ours: Texts.Bytes(), theirs: Texts.Bytes(), decision: Decision}

# the job of merging x and y, two changes of b, in the format f
def Job.of(f: Format, +b: Texts.Bytes(), +x: Texts.Bytes(), +y: Texts.Bytes()) -> Job:
  Job{b, x, y, Format.decide(f, b, x, y)}

# the jobs of the items bs, xs and ys, place by place, in the format f
def Jobs.of(
  bs: List<&2, Texts.Bytes()>,
  +f: Format,
  +xs: List<&2, Texts.Bytes()>,
  +ys: List<&2, Texts.Bytes()>
) -> List<&2, Job>:
  match bs:
    case Nil{}:
      []
    case Con{b, br}:
      Job.of(
        f,
        b,
        Items.first(xs),
        Items.first(ys)
      )
        <> Jobs.of(br, f, List.tail(&2, Texts.Bytes(), xs), List.tail(&2, Texts.Bytes(), ys))

# the change that the decision d takes of x and y, a clash for both
def Merge.taken(d: Decision, x: Texts.Bytes(), y: Texts.Bytes()) -> Merged:
  match d:
    case Decision.Side{Sides.Side.Theirs{}}:
      Merged.Clean{y}
    case Decision.Side{Sides.Side.Ours{}}:
      Merged.Clean{x}
    case e:
      Merged.Clash{}

# the merge of x and y, two changes of b, by lines, with the decision d
def Merge.plain(d: Decision, +b: Texts.Bytes(), +x: Texts.Bytes(), +y: Texts.Bytes()) -> Merged:
  match d:
    case Decision.Side{Sides.Side.Theirs{}}:
      Merged.Clean{y}
    case Decision.Side{Sides.Side.Ours{}}:
      Merged.Clean{x}
    case e:
      Plain.merge.text(
        Bool.and(Plain.is_text(b), Bool.and(Plain.is_text(x), Plain.is_text(y))),
        b,
        x,
        y
      )

# the merge of x and y, two changes of b, in the leaf k, with the decision d
def Leaf.merge(
  k: Leaf,
  d: Decision,
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Merged:
  match k:
    case Leaf.Lines{}:
      Merge.plain(d, b, x, y)
    case Leaf.Whole{}:
      Merge.taken(d, x, y)
    case Leaf.Module{}:
      Merge.taken(d, x, y)

# the bytes x put before the bytes of a clean list m
def Merged.put(
  x: Texts.Bytes(),
  m: Maybe<&2, List<&2, Texts.Bytes()>>
) -> Maybe<&2, List<&2, Texts.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# the bytes of the merges ms, when none clashes
def Merged.all(ms: List<&2, Merged>) -> Maybe<&2, List<&2, Texts.Bytes()>>:
  match ms:
    case Nil{}:
      Some{[]}
    case Con{Merged.Clean{x}, r}:
      Merged.put(x, Merged.all(r))
    case Con{Merged.Clash{}, r}:
      None{}

# the embedding of the shape sh, with the merged texts mt and regions mr
def Merge.pieces(
  op: Texts.Bytes(),
  cl: Texts.Bytes(),
  sh: List<&2, Shape>,
  mt: Maybe<&2, List<&2, Texts.Bytes()>>,
  mr: Maybe<&2, List<&2, Texts.Bytes()>>
) -> Merged:
  match mt mr:
    case Some{ts} Some{rs}:
      Merged.Clean{Embed.join(op, cl, Pieces.build(sh, ts, rs))}
    case _ _:
      Merged.Clash{}

# the first merge of ms, a clash when there is none
def Merged.head(ms: List<&2, Merged>) -> Merged:
  match ms:
    case Nil{}:
      Merged.Clash{}
    case Con{m, r}:
      m

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the merges of the jobs js, in the format f. An embedding of one shape merges
# its texts in the outer format and its regions in the inner one; of other
# shapes, it merges as the outer format.
def Format.merges(f: Format, js: List<&2, Job>) -> List<&2, Merged>:
  match f js:
    case Format.Leaf{k} Nil{}:
      []
    case Format.Leaf{+k} Con{Job{b, x, y, d}, jr}:
      Leaf.merge(k, d, b, x, y) <> Format.merges(Format.Leaf{k}, jr)
    case Format.Embed{o, op, cl, i} Nil{}:
      []
    case Format.Embed{+o, +op, +cl, +i} Con{Job{b, x, y, Decision.Pieces{}}, jr}:
      +pb = Embed.split(op, cl, b)
      +px = Embed.split(op, cl, x)
      +py = Embed.split(op, cl, y)
      jt = Jobs.of(Pieces.texts(pb), o, Pieces.texts(px), Pieces.texts(py))
      jr2 = Jobs.of(Pieces.regions(pb), i, Pieces.regions(px), Pieces.regions(py))
      mt mr rest = Format.merges(
        o,
        jt
      ) Format.merges(i, jr2) Format.merges(Format.Embed{o, op, cl, i}, jr)
      Merge.pieces(op, cl, Pieces.shape(pb), Merged.all(mt), Merged.all(mr)) <> rest
    case Format.Embed{+o, +op, +cl, +i} Con{Job{+b, +x, +y, Decision.Side{Sides.Side.Both{}}}, jr}:
      m rest = Format.merges(o, [Job.of(o, b, x, y)]) Format.merges(Format.Embed{o, op, cl, i}, jr)
      Merged.head(m) <> rest
    case Format.Embed{+o, +op, +cl, +i} Con{Job{b, x, y, d}, jr}:
      Merge.taken(d, x, y) <> Format.merges(Format.Embed{o, op, cl, i}, jr)
    case Format.Code{base, r, im} q:
      Format.merges(base, q)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# the merge of x and y, two changes of b, in the format f
def Format.merge(+f: Format, b: Texts.Bytes(), x: Texts.Bytes(), y: Texts.Bytes()) -> Merged:
  Merged.head(Format.merges(f, [Job.of(f, b, x, y)]))

# a decision that takes z of the changes merges to z, by lines
def Merge.plain_taken(
  d: Decision,
  -b: Texts.Bytes(),
  -x: Texts.Bytes(),
  -y: Texts.Bytes(),
  -z: Texts.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}
) -> {Merge.plain(d, b, x, y) == Merged.Clean{z}: Merged}:
  match d:
    case Decision.Side{Sides.Side.Theirs{}}:
      %Equal.sym(
        Texts.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), y, z, h)
      ): {Merged.Clean{_} == Merged.Clean{z}: Merged}
      {==}
    case Decision.Side{Sides.Side.Ours{}}:
      %Equal.sym(
        Texts.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), x, z, h)
      ): {Merged.Clean{_} == Merged.Clean{z}: Merged}
      {==}
    case Decision.Side{Sides.Side.Both{}}:
      Empty.absurd(
        {Merge.plain(Decision.Side{Sides.Side.Both{}}, b, x, y) == Merged.Clean{z}: Merged},
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )
    case Decision.Pieces{}:
      Empty.absurd(
        {Merge.plain(Decision.Pieces{}, b, x, y) == Merged.Clean{z}: Merged},
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )

# a decision that takes z of the changes takes z
def Merge.taken_taken(
  d: Decision,
  -x: Texts.Bytes(),
  -y: Texts.Bytes(),
  -z: Texts.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}
) -> {Merge.taken(d, x, y) == Merged.Clean{z}: Merged}:
  match d:
    case Decision.Side{Sides.Side.Theirs{}}:
      %Equal.sym(
        Texts.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), y, z, h)
      ): {Merged.Clean{_} == Merged.Clean{z}: Merged}
      {==}
    case Decision.Side{Sides.Side.Ours{}}:
      %Equal.sym(
        Texts.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), x, z, h)
      ): {Merged.Clean{_} == Merged.Clean{z}: Merged}
      {==}
    case Decision.Side{Sides.Side.Both{}}:
      Empty.absurd(
        {Merge.taken(Decision.Side{Sides.Side.Both{}}, x, y) == Merged.Clean{z}: Merged},
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )
    case Decision.Pieces{}:
      Empty.absurd(
        {Merge.taken(Decision.Pieces{}, x, y) == Merged.Clean{z}: Merged},
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )

# a decision that takes z of the changes merges to z, in every leaf
def Leaf.merge_taken(
  k: Leaf,
  -b: Texts.Bytes(),
  -x: Texts.Bytes(),
  -y: Texts.Bytes(),
  -z: Texts.Bytes(),
  d: Decision,
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}
) -> {Leaf.merge(k, d, b, x, y) == Merged.Clean{z}: Merged}:
  match k:
    case Leaf.Lines{}:
      Merge.plain_taken(d, b, x, y, z, h)
    case Leaf.Whole{}:
      Merge.taken_taken(d, x, y, z, h)
    case Leaf.Module{}:
      Merge.taken_taken(d, x, y, z, h)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a job whose decision takes z of its changes merges to z, in every format
def Format.merges_taken(
  f: Format,
  -b: Texts.Bytes(),
  -x: Texts.Bytes(),
  -y: Texts.Bytes(),
  -z: Texts.Bytes(),
  d: Decision,
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}
) -> {Format.merges(f, [Job{b, x, y, d}]) == [Merged.Clean{z}]: List<&2, Merged>}:
  match f d:
    case Format.Leaf{k} e:
      Equal.cong(
        Merged,
        List<&2, Merged>,
        m => [m],
        Leaf.merge(k, e, b, x, y),
        Merged.Clean{z},
        Leaf.merge_taken(k, b, x, y, z, e, h)
      )
    case Format.Embed{o, op, cl, i} Decision.Side{Sides.Side.Theirs{}}:
      %Equal.sym(
        Texts.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), y, z, h)
      ): {[Merged.Clean{_}] == [Merged.Clean{z}]: List<&2, Merged>}
      {==}
    case Format.Embed{o, op, cl, i} Decision.Side{Sides.Side.Ours{}}:
      %Equal.sym(
        Texts.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Texts.Bytes(), x, z, h)
      ): {[Merged.Clean{_}] == [Merged.Clean{z}]: List<&2, Merged>}
      {==}
    case Format.Embed{o, op, cl, i} Decision.Side{Sides.Side.Both{}}:
      Empty.absurd(
        {
          Format.merges(
            Format.Embed{o, op, cl, i},
            [Job{b, x, y, Decision.Side{Sides.Side.Both{}}}]
          )
            == [Merged.Clean{z}]: List<&2, Merged>
        },
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )
    case Format.Embed{o, op, cl, i} Decision.Pieces{}:
      Empty.absurd(
        {
          Format.merges(
            Format.Embed{o, op, cl, i},
            [Job{b, x, y, Decision.Pieces{}}]
          )
            == [Merged.Clean{z}]: List<&2, Merged>
        },
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )
    case Format.Code{base, r, im} e:
      Format.merges_taken(base, b, x, y, z, e, h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a decision that takes z of the changes takes it in every format
def Format.decide.on_taken(
  d: Decision,
  -f: Format,
  -b: Texts.Bytes(),
  -x: Texts.Bytes(),
  -y: Texts.Bytes(),
  -z: Texts.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}
) -> {Decision.take(Format.decide.on(d, f, b, x, y), x, y) == Some{z}: Maybe<&2, Texts.Bytes()>}:
  match d:
    case Decision.Side{Sides.Side.Theirs{}}:
      h
    case Decision.Side{Sides.Side.Ours{}}:
      h
    case Decision.Side{Sides.Side.Both{}}:
      Empty.absurd(
        {
          Decision.take(
            Format.decide.on(Decision.Side{Sides.Side.Both{}}, f, b, x, y),
            x,
            y
          )
            == Some{z}: Maybe<&2, Texts.Bytes()>
        },
        Shared.Maybe.none_ne_some(Texts.Bytes(), z, h)
      )
    case Decision.Pieces{}:
      h

# a merge loses no change that only one side made, in every format: when the
# three-way choice of the change takes z (Sides.Side.keeps_changes says
# which), the merge of the format is z
law Format.merge_takes:
  for +f: Format
  for +b: Texts.Bytes()
  for +x: Texts.Bytes()
  for +y: Texts.Bytes()
  for -z: Texts.Bytes()
  for h: {
    Sides.Side.take(
      Texts.Bytes(),
      Sides.Side.of(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), b, x, y),
      x,
      y
    )
      == Some{z}: Maybe<&2, Texts.Bytes()>
  }
  {Format.merge(f, b, x, y) == Merged.Clean{z}: Merged}

def Format.merge_takes(f, b, x, y, z, h):
  Equal.cong(
    List<&2, Merged>,
    Merged,
    ms => Merged.head(ms),
    Format.merges(f, [Job.of(f, b, x, y)]),
    [Merged.Clean{z}],
    Format.merges_taken(
      f,
      b,
      x,
      y,
      z,
      Format.decide(f, b, x, y),
      Format.decide.on_taken(Merge.decide(b, x, y), f, b, x, y, z, h)
    )
  )

# What a format reads
# -------------------

# what changed from a to b, part by part, as the format f shows it to a
# reader: an embedding shows the changes of its outer format, over all of it
def Format.changes(f: Format, +a: Texts.Bytes(), +b: Texts.Bytes()) -> List<&2, Change>:
  match f:
    case Format.Leaf{Leaf.Lines{}}:
      Plain.changes(a, b)
    case Format.Leaf{k}:
      Plain.changes.whole(Shared.List.is_eq(~U32, ~U32.is_eq, a, b), a, b)
    case Format.Embed{o, op, cl, i}:
      Format.changes(o, a, b)
    case Format.Code{base, r, im}:
      Format.changes(base, a, b)

# the imports of each of the items bs, by the rule r
def Rule.imports.all(bs: List<&2, Texts.Bytes()>, +r: Rule) -> List<&2, Import>:
  match bs:
    case Nil{}:
      []
    case Con{b, br}:
      List.append(&2, Import, Rule.imports.of(r, b), Rule.imports.all(br, r))

# the texts (texts) or the regions of each of the items bs, between the
# markers op and cl
def Embed.parts(
  bs: List<&2, Texts.Bytes()>,
  texts: Bool,
  +op: Texts.Bytes(),
  +cl: Texts.Bytes()
) -> List<&2, Texts.Bytes()>:
  match bs texts:
    case Nil{} t:
      []
    case Con{b, br} True{}:
      List.append(
        &2,
        Texts.Bytes(),
        Pieces.texts(Embed.split(op, cl, b)),
        Embed.parts(br, True{}, op, cl)
      )
    case Con{b, br} False{}:
      List.append(
        &2,
        Texts.Bytes(),
        Pieces.regions(Embed.split(op, cl, b)),
        Embed.parts(br, False{}, op, cl)
      )

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# what the items bs use, in the format f: the edges of each language, in the
# parts that it reads
def Format.uses(f: Format, +bs: List<&2, Texts.Bytes()>) -> List<&2, Import>:
  match f:
    case Format.Leaf{k}:
      []
    case Format.Embed{o, +op, +cl, i}:
      tp = Embed.parts(bs, True{}, op, cl)
      rp = Embed.parts(bs, False{}, op, cl)
      ts rs = Format.uses(o, tp) Format.uses(i, rp)
      List.append(&2, Import, ts, rs)
    case Format.Code{base, r, im}:
      List.append(
        &2,
        Import,
        Rule.imports.all(bs, r),
        List.append(&2, Import, im, Format.uses(base, bs))
      )
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# Items
# -----
# A format splits a resource into items (Item): functions, types, sections.
# What a writer's work uses is then a set of items, not of whole resources. A
# format that cannot split a resource gives the whole resource as one item
# with no name, which uses all that the resource imports: so a language
# without a splitter is tracked per resource, and never misses a use.

# the items of the bytes b in the format f. No format splits yet: each gives
# the whole resource as one item
def Format.items(f: Format, b: Texts.Bytes()) -> List<&2, Item>:
  [Item{"content", [], 0n, b, []}]

# the item x is one of those that the names ns ask for
def Item.asked(ns: List<&2, Texts.Bytes()>, x: Item) -> Bool:
  match x:
    case Item{k, n, at, b, us}:
      List.contains(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), ns, n)

# the items of xs that the names ns ask for
def Items.asked(+ns: List<&2, Texts.Bytes()>, xs: List<&2, Item>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.filter.put(Item, x, Items.asked(ns, rest), Item.asked(ns, x))

# the items of its target xs that the import x brings into scope: only those
# that it names, when it brings only named items and names some; else all of
# them. An item with no name is the whole resource, which every import brings
def Import.pool(x: Import, xs: List<&2, Item>) -> List<&2, Item>:
  match x:
    case Import{Edge{t, al, Con{n, more}, cs}, Brings.Named{}, fi}:
      Items.asked(Con{n, more}, xs)
    case _:
      xs

# The code of a format
# --------------------
# A format is data: a resource keeps its own, by hash, so every node reads a
# resource in the same format, whatever its name.

# the condition c, then r
def Cond.code(c: Cond, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Cond{x, h}:
      Codes.Code.words(x, Codes.Code.bool(h, r))

# a condition
def Cond.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Cond>>:
  Codes.Code.two.read(
    ~Texts.Bytes(),
    ~Bool,
    ~Cond,
    ~Codes.Code.words.read,
    ~Codes.Code.bool.read,
    x => h => Cond{x, h},
    ts
  )

# a condition reads back
def Cond.code_read(
  c: Cond,
  r: List<&2, U32>
) -> {Cond.code.read(Cond.code(c, r)) == Some{Codes.Read{c, r}}: Maybe<&2, Codes.Read<Cond>>}:
  match c:
    case Cond{x, h}:
      Codes.Code.two_read(
        ~Texts.Bytes(),
        ~Bool,
        ~Cond,
        ~Codes.Code.words.codec(),
        ~Codes.Code.bool.codec(),
        a => b => Cond{a, b},
        x,
        h,
        r
      )

# the code of conditions
def Cond.codec() -> Codes.Codec(Cond):
  (Cond.code, (Cond.code.read, c => r => Cond.code_read(c, r)))

# the edge e, then r
def Edge.code(e: Edge, r: List<&2, U32>) -> List<&2, U32>:
  match e:
    case Edge{t, a, ns, cs}:
      Codes.Code.words(
        t,
        Codes.Code.words(
          a,
          Codes.Code.list(
            ~Texts.Bytes(),
            ~Codes.Code.words,
            ns,
            Codes.Code.list(~Cond, ~Cond.code, cs, r)
          )
        )
      )

# an edge
def Edge.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Edge>>:
  Codes.Code.four.read(
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~List<&2, Texts.Bytes()>,
    ~List<&2, Cond>,
    ~Edge,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~(m => Codes.Code.list.read(~Texts.Bytes(), ~Codes.Code.words.read, m)),
    ~(m => Codes.Code.list.read(~Cond, ~Cond.code.read, m)),
    t => a => ns => cs => Edge{t, a, ns, cs},
    ts
  )

# an edge reads back
def Edge.code_read(
  e: Edge,
  r: List<&2, U32>
) -> {Edge.code.read(Edge.code(e, r)) == Some{Codes.Read{e, r}}: Maybe<&2, Codes.Read<Edge>>}:
  match e:
    case Edge{t, a, ns, cs}:
      Codes.Code.four_read(
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~List<&2, Texts.Bytes()>,
        ~List<&2, Cond>,
        ~Edge,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Codes.Code.list.codec(~Texts.Bytes(), ~Codes.Code.words.codec()),
        ~Codes.Code.list.codec(~Cond, ~Cond.codec()),
        w => x => y => z => Edge{w, x, y, z},
        t,
        a,
        ns,
        cs,
        r
      )

# the code of edges
def Edge.codec() -> Codes.Codec(Edge):
  (Edge.code, (Edge.code.read, e => r => Edge.code_read(e, r)))

# what an import brings, then r
def Brings.code(b: Brings, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Brings.Named{}:
      0 <> r
    case Brings.Whole{}:
      1 <> r
    case Brings.Through{}:
      2 <> r

# what an import brings
def Brings.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Brings>>:
  match ts:
    case Con{0, r}:
      Some{Codes.Read{Brings.Named{}, r}}
    case Con{1, r}:
      Some{Codes.Read{Brings.Whole{}, r}}
    case Con{2, r}:
      Some{Codes.Read{Brings.Through{}, r}}
    case _:
      None{}

# what an import brings reads back
def Brings.code_read(
  b: Brings,
  r: List<&2, U32>
) -> {Brings.code.read(Brings.code(b, r)) == Some{Codes.Read{b, r}}: Maybe<&2, Codes.Read<Brings>>}:
  match b:
    case Brings.Named{}:
      {==}
    case Brings.Whole{}:
      {==}
    case Brings.Through{}:
      {==}

# the code of what imports bring
def Brings.codec() -> Codes.Codec(Brings):
  (Brings.code, (Brings.code.read, b => r => Brings.code_read(b, r)))

# how a target is found, then r
def Find.code(f: Find, r: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Find{s, l, rs, ss}:
      Codes.Code.maybe(
        ~Char,
        ~Codes.Code.char,
        s,
        Codes.Code.bool(
          l,
          Codes.Code.list(
            ~String,
            ~Codes.Code.text,
            rs,
            Codes.Code.list(~String, ~Codes.Code.text, ss, r)
          )
        )
      )

# how a target is found
def Find.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Find>>:
  Codes.Code.four.read(
    ~Maybe<&2, Char>,
    ~Bool,
    ~List<&2, String>,
    ~List<&2, String>,
    ~Find,
    ~(m => Codes.Code.maybe.read(~Char, ~Codes.Code.char.read, m)),
    ~Codes.Code.bool.read,
    ~(m => Codes.Code.list.read(~String, ~Codes.Code.text.read, m)),
    ~(m => Codes.Code.list.read(~String, ~Codes.Code.text.read, m)),
    s => l => rs => ss => Find{s, l, rs, ss},
    ts
  )

# how a target is found reads back
def Find.code_read(
  f: Find,
  r: List<&2, U32>
) -> {Find.code.read(Find.code(f, r)) == Some{Codes.Read{f, r}}: Maybe<&2, Codes.Read<Find>>}:
  match f:
    case Find{s, l, rs, ss}:
      Codes.Code.four_read(
        ~Maybe<&2, Char>,
        ~Bool,
        ~List<&2, String>,
        ~List<&2, String>,
        ~Find,
        ~Codes.Code.maybe.codec(~Char, ~Codes.Code.char.codec()),
        ~Codes.Code.bool.codec(),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        w => x => y => z => Find{w, x, y, z},
        s,
        l,
        rs,
        ss,
        r
      )

# the code of how targets are found
def Find.codec() -> Codes.Codec(Find):
  (Find.code, (Find.code.read, f => r => Find.code_read(f, r)))

# the import x, then r
def Import.code(x: Import, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Import{e, b, f}:
      Edge.code(e, Brings.code(b, Find.code(f, r)))

# an import
def Import.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Import>>:
  Codes.Code.three.read(
    ~Edge,
    ~Brings,
    ~Find,
    ~Import,
    ~Edge.code.read,
    ~Brings.code.read,
    ~Find.code.read,
    e => b => f => Import{e, b, f},
    ts
  )

# an import reads back
def Import.code_read(
  x: Import,
  r: List<&2, U32>
) -> {Import.code.read(Import.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Import>>}:
  match x:
    case Import{e, b, f}:
      Codes.Code.three_read(
        ~Edge,
        ~Brings,
        ~Find,
        ~Import,
        ~Edge.codec(),
        ~Brings.codec(),
        ~Find.codec(),
        u => v => w => Import{u, v, w},
        e,
        b,
        f,
        r
      )

# the code of imports
def Import.codec() -> Codes.Codec(Import):
  (Import.code, (Import.code.read, x => r => Import.code_read(x, r)))

# the markers of a rule
type Marks is Data:
  Marks{start: Texts.Bytes(), open: Texts.Bytes(), close: Texts.Bytes(), alias: Texts.Bytes()}

# the markers of conditions, what a rule brings, and how it finds targets
type Tail is Data:
  Tail{
    when: Texts.Bytes(),
    otherwise: Texts.Bytes(),
    end: Texts.Bytes(),
    brings: Brings,
    find: Find
  }

# the markers m, then r
def Marks.code(m: Marks, r: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Marks{st, op, cl, al}:
      Codes.Code.words(st, Codes.Code.words(op, Codes.Code.words(cl, Codes.Code.words(al, r))))

# the markers of a rule
def Marks.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Marks>>:
  Codes.Code.four.read(
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~Marks,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    st => op => cl => al => Marks{st, op, cl, al},
    ts
  )

# the markers of a rule read back
def Marks.code_read(
  m: Marks,
  r: List<&2, U32>
) -> {Marks.code.read(Marks.code(m, r)) == Some{Codes.Read{m, r}}: Maybe<&2, Codes.Read<Marks>>}:
  match m:
    case Marks{st, op, cl, al}:
      Codes.Code.four_read(
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~Marks,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        w => x => y => z => Marks{w, x, y, z},
        st,
        op,
        cl,
        al,
        r
      )

# the code of markers
def Marks.codec() -> Codes.Codec(Marks):
  (Marks.code, (Marks.code.read, m => r => Marks.code_read(m, r)))

# the tail x, then r
def Tail.code(x: Tail, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Tail{wh, ot, en, br, fi}:
      Codes.Code.words(
        wh,
        Codes.Code.words(ot, Codes.Code.words(en, Brings.code(br, Find.code(fi, r))))
      )

# the end of a rule
def Tail.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Tail>>:
  Codes.Code.five.read(
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~Texts.Bytes(),
    ~Brings,
    ~Find,
    ~Tail,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~Brings.code.read,
    ~Find.code.read,
    wh => ot => en => br => fi => Tail{wh, ot, en, br, fi},
    ts
  )

# the end of a rule reads back
def Tail.code_read(
  x: Tail,
  r: List<&2, U32>
) -> {Tail.code.read(Tail.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Tail>>}:
  match x:
    case Tail{wh, ot, en, br, fi}:
      Codes.Code.five_read(
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~Texts.Bytes(),
        ~Brings,
        ~Find,
        ~Tail,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Brings.codec(),
        ~Find.codec(),
        v => w => y => z => q => Tail{v, w, y, z, q},
        wh,
        ot,
        en,
        br,
        fi,
        r
      )

# the code of ends of rules
def Tail.codec() -> Codes.Codec(Tail):
  (Tail.code, (Tail.code.read, x => r => Tail.code_read(x, r)))

# the rule of the markers m and the tail x
def Rule.of(m: Marks, x: Tail) -> Rule:
  match m x:
    case Marks{st, op, cl, al} Tail{wh, ot, en, br, fi}:
      Rule{st, op, cl, al, wh, ot, en, br, fi}

# the rule x, then r: its markers, then its tail
def Rule.code(x: Rule, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Rule{st, op, cl, al, wh, ot, en, br, fi}:
      Marks.code(Marks{st, op, cl, al}, Tail.code(Tail{wh, ot, en, br, fi}, r))

# a rule
def Rule.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Rule>>:
  Codes.Code.two.read(
    ~Marks,
    ~Tail,
    ~Rule,
    ~Marks.code.read,
    ~Tail.code.read,
    m => x => Rule.of(m, x),
    ts
  )

# a rule reads back
def Rule.code_read(
  x: Rule,
  r: List<&2, U32>
) -> {Rule.code.read(Rule.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Rule>>}:
  match x:
    case Rule{st, op, cl, al, wh, ot, en, br, fi}:
      Codes.Code.two_read(
        ~Marks,
        ~Tail,
        ~Rule,
        ~Marks.codec(),
        ~Tail.codec(),
        m => t => Rule.of(m, t),
        Marks{st, op, cl, al},
        Tail{wh, ot, en, br, fi},
        r
      )

# the code of rules
def Rule.codec() -> Codes.Codec(Rule):
  (Rule.code, (Rule.code.read, x => r => Rule.code_read(x, r)))

# the leaf k, then r
def Leaf.code(k: Leaf, r: List<&2, U32>) -> List<&2, U32>:
  match k:
    case Leaf.Lines{}:
      0 <> r
    case Leaf.Whole{}:
      1 <> r
    case Leaf.Module{}:
      2 <> r

# a leaf
def Leaf.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Leaf>>:
  match ts:
    case Con{0, r}:
      Some{Codes.Read{Leaf.Lines{}, r}}
    case Con{1, r}:
      Some{Codes.Read{Leaf.Whole{}, r}}
    case Con{2, r}:
      Some{Codes.Read{Leaf.Module{}, r}}
    case _:
      None{}

# a leaf reads back
def Leaf.code_read(
  k: Leaf,
  r: List<&2, U32>
) -> {Leaf.code.read(Leaf.code(k, r)) == Some{Codes.Read{k, r}}: Maybe<&2, Codes.Read<Leaf>>}:
  match k:
    case Leaf.Lines{}:
      {==}
    case Leaf.Whole{}:
      {==}
    case Leaf.Module{}:
      {==}

# the code of leaves
def Leaf.codec() -> Codes.Codec(Leaf):
  (Leaf.code, (Leaf.code.read, k => r => Leaf.code_read(k, r)))

# the count of the formats in f: itself and each that it holds
def Format.size(f: Format) -> Nat:
  match f:
    case Format.Leaf{k}:
      1n
    case Format.Embed{o, op, cl, i}:
      so si = Format.size(o) Format.size(i)
      1n+Nat.add(so, si)
    case Format.Code{b, x, im}:
      1n+Format.size(b)

# the parts of the format f, then r: its tag, then what its kind holds
def Format.body(f: Format, r: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Format.Leaf{k}:
      0 <> Leaf.code(k, r)
    case Format.Embed{o, op, cl, i}:
      1 <> Format.body(o, Codes.Code.words(op, Codes.Code.words(cl, Format.body(i, r))))
    case Format.Code{b, x, im}:
      2 <> Format.body(b, Rule.code(x, Codes.Code.list(~Import, ~Import.code, im, r)))

# the format f, then r: its size, then its parts, so that a read of it ends
def Format.code(f: Format, r: List<&2, U32>) -> List<&2, U32>:
  +f = f
  Codes.Code.count(Format.size(f), Format.body(f, r))

# the parts of a format of at most f formats: each step reads one tag, then
# the parts of its kind
def Format.code.read.go(f: Nat, ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Format>>:
  match f ts:
    case 0n x:
      None{}
    case 1n+p Nil{}:
      None{}
    case 1n+(+p) Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Format>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~Leaf, ~Format, ~Leaf.code.read, k => Format.Leaf{k}, r),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Format>>,
          U32.is_eq(x, 1),
          v => Codes.Read.then(
            Format,
            Format,
            Format.code.read.go(p, r),
            o => r1 => Codes.Read.then(
              Texts.Bytes(),
              Format,
              Codes.Code.words.read(r1),
              op => r2 => Codes.Read.then(
                Texts.Bytes(),
                Format,
                Codes.Code.words.read(r2),
                cl => r3 => Codes.Read.then(
                  Format,
                  Format,
                  Format.code.read.go(p, r3),
                  i => r4 => Some{Codes.Read{Format.Embed{o, op, cl, i}, r4}}
                )
              )
            )
          ),
          v => Shared.Bool.when(
            Maybe<&2, Codes.Read<Format>>,
            U32.is_eq(x, 2),
            w => Codes.Read.then(
              Format,
              Format,
              Format.code.read.go(p, r),
              b => r1 => Codes.Code.two.read(
                ~Rule,
                ~List<&2, Import>,
                ~Format,
                ~Rule.code.read,
                ~(m => Codes.Code.list.read(~Import, ~Import.code.read, m)),
                x2 => im => Format.Code{b, x2, im},
                r1
              )
            ),
            w => None{}
          )
        )
      )

# a format: its size, then its parts
def Format.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Format>>:
  Codes.Read.then(Nat, Format, Codes.Code.count.read(ts), n => r => Format.code.read.go(n, r))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the parts of a format read back, in as many steps as it has formats, or more
def Format.body_read(
  f: Format,
  +r: List<&2, U32>,
  p: Nat,
  +h: {Nat.is_le(Format.size(f), p) == True{}: Bool}
) -> {
  Format.code.read.go(p, Format.body(f, r)) == Some{Codes.Read{f, r}}: Maybe<&2, Codes.Read<Format>>
}:
  match f p:
    case Format.Leaf{k} 0n:
      Empty.absurd(
        {
          Format.code.read.go(
            0n,
            Format.body(Format.Leaf{k}, r)
          )
            == Some{Codes.Read{Format.Leaf{k}, r}}: Maybe<&2, Codes.Read<Format>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Format.Leaf{k} 1n+q:
      Codes.Code.one_read(~Leaf, ~Format, ~Leaf.codec(), x => Format.Leaf{x}, k, r)
    case Format.Embed{o, op, cl, i} 0n:
      Empty.absurd(
        {
          Format.code.read.go(
            0n,
            Format.body(Format.Embed{o, op, cl, i}, r)
          )
            == Some{Codes.Read{Format.Embed{o, op, cl, i}, r}}: Maybe<&2, Codes.Read<Format>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Format.Embed{+o, +op, +cl, +i} 1n+(+q):
      +so = Format.size(o)
      +si = Format.size(i)
      +ri = Format.body(i, r)
      +rc = Codes.Code.words(cl, ri)
      w = Codes.Code.words(op, rc)
      e = {Some{Codes.Read{Format.Embed{o, op, cl, i}, r}}: Maybe<&2, Codes.Read<Format>>}
      %Codes.Read.then_some(
        Format,
        Format,
        Format.code.read.go(q, Format.body(o, w)),
        o2 => r1 => Codes.Read.then(
          Texts.Bytes(),
          Format,
          Codes.Code.words.read(r1),
          op2 => r2 => Codes.Read.then(
            Texts.Bytes(),
            Format,
            Codes.Code.words.read(r2),
            cl2 => r3 => Codes.Read.then(
              Format,
              Format,
              Format.code.read.go(q, r3),
              i2 => r4 => Some{Codes.Read{Format.Embed{o2, op2, cl2, i2}, r4}}
            )
          )
        ),
        o,
        w,
        Format.body_read(
          o,
          w,
          q,
          Shared.Nat.le_trans(so, Nat.add(so, si), q)(Shared.Nat.le_add_first(so, si))(h)
        )
      ): {_ == e: Maybe<&2, Codes.Read<Format>>}
      %Codes.Read.then_some(
        Texts.Bytes(),
        Format,
        Codes.Code.words.read(w),
        op2 => r2 => Codes.Read.then(
          Texts.Bytes(),
          Format,
          Codes.Code.words.read(r2),
          cl2 => r3 => Codes.Read.then(
            Format,
            Format,
            Format.code.read.go(q, r3),
            i2 => r4 => Some{Codes.Read{Format.Embed{o, op2, cl2, i2}, r4}}
          )
        ),
        op,
        rc,
        Codes.Codec.laws(List<&2, U32>, Codes.Code.words.codec())(op)(rc)
      ): {_ == e: Maybe<&2, Codes.Read<Format>>}
      %Codes.Read.then_some(
        Texts.Bytes(),
        Format,
        Codes.Code.words.read(rc),
        cl2 => r3 => Codes.Read.then(
          Format,
          Format,
          Format.code.read.go(q, r3),
          i2 => r4 => Some{Codes.Read{Format.Embed{o, op, cl2, i2}, r4}}
        ),
        cl,
        ri,
        Codes.Codec.laws(List<&2, U32>, Codes.Code.words.codec())(cl)(ri)
      ): {_ == e: Maybe<&2, Codes.Read<Format>>}
      %Codes.Read.then_some(
        Format,
        Format,
        Format.code.read.go(q, ri),
        i2 => r4 => Some{Codes.Read{Format.Embed{o, op, cl, i2}, r4}},
        i,
        r,
        Format.body_read(
          i,
          r,
          q,
          Shared.Nat.le_trans(si, Nat.add(so, si), q)(Shared.Nat.le_add(so, si))(h)
        )
      ): {_ == e: Maybe<&2, Codes.Read<Format>>}
      {==}
    case Format.Code{b, x, im} 0n:
      Empty.absurd(
        {
          Format.code.read.go(
            0n,
            Format.body(Format.Code{b, x, im}, r)
          )
            == Some{Codes.Read{Format.Code{b, x, im}, r}}: Maybe<&2, Codes.Read<Format>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Format.Code{+b, +x, +im} 1n+q:
      rb = Rule.code(x, Codes.Code.list(~Import, ~Import.code, im, r))
      %Codes.Read.then_some(
        Format,
        Format,
        Format.code.read.go(q, Format.body(b, rb)),
        b2 => r1 => Codes.Code.two.read(
          ~Rule,
          ~List<&2, Import>,
          ~Format,
          ~Rule.code.read,
          ~(m => Codes.Code.list.read(~Import, ~Import.code.read, m)),
          x2 => im2 => Format.Code{b2, x2, im2},
          r1
        ),
        b,
        rb,
        Format.body_read(b, rb, q, h)
      ): {_ == Some{Codes.Read{Format.Code{b, x, im}, r}}: Maybe<&2, Codes.Read<Format>>}
      Codes.Code.two_read(
        ~Rule,
        ~List<&2, Import>,
        ~Format,
        ~Rule.codec(),
        ~Codes.Code.list.codec(~Import, ~Import.codec()),
        x2 => im2 => Format.Code{b, x2, im2},
        x,
        im,
        r
      )

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a format reads back from its code
law Format.code_read:
  for +f: Format
  for +r: List<&2, U32>
  {Format.code.read(Format.code(f, r)) == Some{Codes.Read{f, r}}: Maybe<&2, Codes.Read<Format>>}

def Format.code_read(f, r):
  %Codes.Read.then_some(
    Nat,
    Format,
    Codes.Code.count.read(Codes.Code.count(Format.size(f), Format.body(f, r))),
    n => r1 => Format.code.read.go(n, r1),
    Format.size(f),
    Format.body(f, r),
    Codes.Code.count_read(Format.size(f), Format.body(f, r))
  ): {_ == Some{Codes.Read{f, r}}: Maybe<&2, Codes.Read<Format>>}
  Format.body_read(f, r, Format.size(f), Shared.Nat.le_refl(Format.size(f)))

# the code of formats
def Format.codec() -> Codes.Codec(Format):
  (Format.code, (Format.code.read, f => r => Format.code_read(f, r)))

# Known formats
# -------------

# a language whose imports name a target after start, up to close, bring br
# and are found by fi
def Format.imports(
  start: String,
  open: String,
  close: String,
  alias: String,
  br: Brings,
  fi: Find
) -> Format:
  Format.Code{
    Format.Leaf{Leaf.Lines{}},
    Rule{
      Texts.Bytes.of_text(start),
      Texts.Bytes.of_text(open),
      Texts.Bytes.of_text(close),
      Texts.Bytes.of_text(alias),
      [],
      [],
      [],
      br,
      fi
    },
    []
  }

# a target that is a path beside the resource, with the suffixes ss
def Find.beside(ss: List<&2, String>) -> Find:
  Find{None{}, True{}, [], ss}

# the format of the paths that end with a suffix
type Known is Data:
  Known{suffix: String, format: Format}

# the formats of the paths that end with each suffix
def Format.known() -> List<&2, Known>:
  +oftext1 = Texts.Bytes.of_text("```")
  +oftext2 = Texts.Bytes.of_text("\"")
  +css = Format.imports("@import ", "\"", "\"", "", Brings.Through{}, Find.beside([""]))
  +js = Format.imports(
    "import ",
    "from \"",
    "\"",
    "",
    Brings.Named{},
    Find{None{}, True{}, ["node_modules"], ["", ".js", ".ts", "/index.js"]}
  )
  +c: Format = Format.Code{
    Format.Leaf{Leaf.Lines{}},
    Rule{
      Texts.Bytes.of_text("#include"),
      oftext2,
      oftext2,
      [],
      Texts.Bytes.of_text("#if"),
      Texts.Bytes.of_text("#else"),
      Texts.Bytes.of_text("#endif"),
      Brings.Through{},
      Find.beside([""])
    },
    []
  }
  +html: Format = Format.Embed{
    Format.Embed{
      Format.imports("<script src=\"", "", "\"", "", Brings.Whole{}, Find.beside([""])),
      Texts.Bytes.of_text("<style>"),
      Texts.Bytes.of_text("</style>"),
      css
    },
    Texts.Bytes.of_text("<script>"),
    Texts.Bytes.of_text("</script>"),
    js
  }
  [
    Known{".bend", Format.imports("import ", "", " ", "as ", Brings.Whole{}, Find.beside([""]))},
    Known{".c", c},
    Known{".h", c},
    Known{".js", js},
    Known{".mjs", js},
    Known{".ts", js},
    Known{".css", css},
    Known{".html", html},
    Known{".htm", html},
    Known{".module", Format.Leaf{Leaf.Module{}}},
    Known{".png", Format.Leaf{Leaf.Whole{}}},
    Known{".jpg", Format.Leaf{Leaf.Whole{}}},
    Known{".gif", Format.Leaf{Leaf.Whole{}}},
    Known{".pdf", Format.Leaf{Leaf.Whole{}}},
    Known{".zip", Format.Leaf{Leaf.Whole{}}},
    Known{".wasm", Format.Leaf{Leaf.Whole{}}},
    Known{
      ".md",
      Format.Embed{Format.Leaf{Leaf.Lines{}}, oftext1, oftext1, Format.Leaf{Leaf.Lines{}}}
    }
  ]

# the format of the first suffix of ks that the path p ends with: lines when
# none does
def Format.find(ks: List<&2, Known>, +p: String) -> Format:
  match ks:
    case Nil{}:
      Format.Leaf{Leaf.Lines{}}
    case Con{Known{k, f}, r}:
      Shared.Bool.when(Format, String.ends_with(p, k), u => f, u => Format.find(r, p))

# a format to suggest for a new resource named p, by its suffix. A resource
# keeps its format as data: no node reads a format from a name
def Format.guess(p: String) -> Format:
  Format.find(Format.known(), p)
