import Base
import ./shared.bend as Shared

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
  s: Shared.Bytes() & List<&2, Shared.Bytes()>
) -> Shared.Bytes()
  & List<&2, Shared.Bytes()>:
  match nl s:
    case True{} Tuple{l, ls}:
      ([], l <> ls)
    case False{} Tuple{l, ls}:
      (c <> l, ls)

# the lines of b, split at each '\n', as the line it starts with and the rest
def Lines.split(b: Shared.Bytes()) -> Shared.Bytes() & List<&2, Shared.Bytes()>:
  match b:
    case Nil{}:
      ([], [])
    case Con{+c, r}:
      Lines.split.on(U32.is_eq(c, 10), c, Lines.split(r))

# the bytes of the line l and then the lines ls, with a '\n' between each
def Lines.join(ls: List<&2, Shared.Bytes()>, l: Shared.Bytes()) -> Shared.Bytes():
  match ls:
    case Nil{}:
      l
    case Con{n, r}:
      List.append(&2, U32, l, 10 <> Lines.join(r, n))

# the bytes of a split
def Lines.join.of(s: Shared.Bytes() & List<&2, Shared.Bytes()>) -> Shared.Bytes():
  match s:
    case Tuple{l, ls}:
      Lines.join(ls, l)

# a byte before the first line comes first
def Lines.join_cons(
  ls: List<&2, Shared.Bytes()>,
  c: U32,
  l: Shared.Bytes()
) -> {Lines.join(ls, c <> l) == c <> Lines.join(ls, l): Shared.Bytes()}:
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
  s: Shared.Bytes() & List<&2, Shared.Bytes()>,
  r: Shared.Bytes(),
  e: {U32.is_eq(c, 10) == nl: Bool},
  ih: {Lines.join.of(s) == r: Shared.Bytes()}
) -> {Lines.join.of(Lines.split.on(nl, c, s)) == c <> r: Shared.Bytes()}:
  match nl s:
    case True{} Tuple{l, ls}:
      %Equal.sym(
        U32,
        c,
        10,
        Shared.U32.is_eq_sound(c, 10)(e)
      ): {10 <> Lines.join(ls, l) == _ <> r: Shared.Bytes()}
      %ih: {10 <> Lines.join(ls, l) == 10 <> _: Shared.Bytes()}
      {==}
    case False{} Tuple{l, ls}:
      %Equal.sym(
        Shared.Bytes(),
        Lines.join(ls, c <> l),
        c <> Lines.join(ls, l),
        Lines.join_cons(ls, c, l)
      ):
        {_ == c <> r: Shared.Bytes()}
      %ih: {c <> Lines.join(ls, l) == c <> _: Shared.Bytes()}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines of b join back into b
law Lines.read_back:
  for b: Shared.Bytes()
  {Lines.join.of(Lines.split(b)) == b: Shared.Bytes()}

def Lines.read_back(b):
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
    start: List<&2, Shared.Bytes()>,
    old: List<&2, Shared.Bytes()>,
    new: List<&2, Shared.Bytes()>,
    end: List<&2, Shared.Bytes()>
  }

# the old lines of c, between its start and end
def Cut.left(c: Cut) -> List<&2, Shared.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Shared.Bytes(), s, List.append(&2, Shared.Bytes(), o, e))

# the new lines of c, between its start and end
def Cut.right(c: Cut) -> List<&2, Shared.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Shared.Bytes(), s, List.append(&2, Shared.Bytes(), n, e))

# the cut with the start s and the ends e
def Lines.cut.ends(s: List<&2, Shared.Bytes()>, e: Shared.Ends<Shared.Bytes()>) -> Cut:
  match e:
    case Shared.Ends{ea, eb, se}:
      Cut{s, ea, eb, se}

# the cut of a fork, by the ends of what follows its shared start
def Lines.cut.of(f: Shared.Fork<Shared.Bytes()>) -> Cut:
  match f:
    case Shared.Fork{s, ra, rb}:
      Lines.cut.ends(s, Shared.List.ends(~Shared.Bytes(), ~Shared.Bytes.is_eq, ra, rb))

# the lines that a and b share at the start and at the end, and what differs
def Lines.cut(a: List<&2, Shared.Bytes()>, b: List<&2, Shared.Bytes()>) -> Cut:
  Lines.cut.of(Shared.List.fork(~Shared.Bytes(), ~Shared.Bytes.is_eq, a, b))

# the old lines of a cut by ends e are its start, then the first list of e
def Lines.cut.ends_left(
  s: List<&2, Shared.Bytes()>,
  e: Shared.Ends<Shared.Bytes()>
) -> {
  Cut.left(
    Lines.cut.ends(s, e)
  )
    == List.append(
      &2,
      Shared.Bytes(),
      s,
      Shared.Ends.left(Shared.Bytes(), e)
    ): List<&2, Shared.Bytes()>
}:
  match e:
    case Shared.Ends{ea, eb, se}:
      {==}

# the new lines of a cut by ends e are its start, then the second list of e
def Lines.cut.ends_right(
  s: List<&2, Shared.Bytes()>,
  e: Shared.Ends<Shared.Bytes()>
) -> {
  Cut.right(
    Lines.cut.ends(s, e)
  )
    == List.append(
      &2,
      Shared.Bytes(),
      s,
      Shared.Ends.right(Shared.Bytes(), e)
    ): List<&2, Shared.Bytes()>
}:
  match e:
    case Shared.Ends{ea, eb, se}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the old lines of the cut of a fork are its first list
def Lines.cut.of_left(
  f: Shared.Fork<Shared.Bytes()>
) -> {Cut.left(Lines.cut.of(f)) == Shared.Fork.left(Shared.Bytes(), f): List<&2, Shared.Bytes()>}:
  match f:
    case Shared.Fork{s, +ra, +rb}:
      e = Shared.List.ends(~Shared.Bytes(), ~Shared.Bytes.is_eq, ra, rb)
      Equal.trans(
        List<&2, Shared.Bytes()>,
        Cut.left(Lines.cut.ends(s, e)),
        List.append(&2, Shared.Bytes(), s, Shared.Ends.left(Shared.Bytes(), e)),
        List.append(&2, Shared.Bytes(), s, ra),
        Lines.cut.ends_left(s, e),
        Equal.cong(
          List<&2, Shared.Bytes()>,
          List<&2, Shared.Bytes()>,
          z => List.append(&2, Shared.Bytes(), s, z),
          Shared.Ends.left(Shared.Bytes(), e),
          ra,
          Shared.List.ends_left(~Shared.Bytes(), ~Shared.Bytes.is_eq, ra, rb)
        )
      )

# the new lines of the cut of a fork are its second list
def Lines.cut.of_right(
  f: Shared.Fork<Shared.Bytes()>
) -> {Cut.right(Lines.cut.of(f)) == Shared.Fork.right(Shared.Bytes(), f): List<&2, Shared.Bytes()>}:
  match f:
    case Shared.Fork{s, +ra, +rb}:
      e = Shared.List.ends(~Shared.Bytes(), ~Shared.Bytes.is_eq, ra, rb)
      Equal.trans(
        List<&2, Shared.Bytes()>,
        Cut.right(Lines.cut.ends(s, e)),
        List.append(&2, Shared.Bytes(), s, Shared.Ends.right(Shared.Bytes(), e)),
        List.append(&2, Shared.Bytes(), s, rb),
        Lines.cut.ends_right(s, e),
        Equal.cong(
          List<&2, Shared.Bytes()>,
          List<&2, Shared.Bytes()>,
          z => List.append(&2, Shared.Bytes(), s, z),
          Shared.Ends.right(Shared.Bytes(), e),
          rb,
          Shared.List.ends_right(
            ~Shared.Bytes(),
            ~Shared.Bytes.is_eq,
            ~Shared.Bytes.is_eq_sound,
            ra,
            rb
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the old lines
law Lines.cut_left:
  for +a: List<&2, Shared.Bytes()>
  for +b: List<&2, Shared.Bytes()>
  {Cut.left(Lines.cut(a, b)) == a: List<&2, Shared.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_left(a, b):
  f = Shared.List.fork(~Shared.Bytes(), ~Shared.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Shared.Bytes()>,
    Cut.left(Lines.cut.of(f)),
    Shared.Fork.left(Shared.Bytes(), f),
    a,
    Lines.cut.of_left(f),
    Shared.List.fork_left(~Shared.Bytes(), ~Shared.Bytes.is_eq, a, b)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the new lines
law Lines.cut_right:
  for +a: List<&2, Shared.Bytes()>
  for +b: List<&2, Shared.Bytes()>
  {Cut.right(Lines.cut(a, b)) == b: List<&2, Shared.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_right(a, b):
  f = Shared.List.fork(~Shared.Bytes(), ~Shared.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Shared.Bytes()>,
    Cut.right(Lines.cut.of(f)),
    Shared.Fork.right(Shared.Bytes(), f),
    b,
    Lines.cut.of_right(f),
    Shared.List.fork_right(~Shared.Bytes(), ~Shared.Bytes.is_eq, ~Shared.Bytes.is_eq_sound, a, b)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines a after a patch: keep the first keep lines, drop the next drop, and
# put the lines put in their place
def Lines.apply(
  keep: Nat,
  a: List<&2, Shared.Bytes()>,
  drop: Nat,
  put: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  match keep a:
    case 0n x:
      List.append(&2, Shared.Bytes(), put, List.drop(&2, Shared.Bytes(), x, drop))
    case 1n+k Nil{}:
      put
    case 1n+k Con{l, r}:
      l <> Lines.apply(k, r, drop, put)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# applying the patch of a cut to its old lines gives its new lines
def Lines.apply_cut(
  s: List<&2, Shared.Bytes()>,
  o: List<&2, Shared.Bytes()>,
  n: List<&2, Shared.Bytes()>,
  e: List<&2, Shared.Bytes()>
) -> {
  Lines.apply(
    List.length(&2, Shared.Bytes(), s),
    Cut.left(Cut{s, o, n, e}),
    List.length(&2, Shared.Bytes(), o),
    n
  )
    == Cut.right(Cut{s, o, n, e}): List<&2, Shared.Bytes()>
}:
  match s:
    case Nil{}:
      %Equal.sym(
        List<&2, Shared.Bytes()>,
        List.drop(
          &2,
          Shared.Bytes(),
          List.append(&2, Shared.Bytes(), o, e),
          List.length(&2, Shared.Bytes(), o)
        ),
        e,
        Shared.List.drop_after_append(Shared.Bytes(), o, e)
      ):
        {
          List.append(
            &2,
            Shared.Bytes(),
            n,
            _
          )
            == List.append(&2, Shared.Bytes(), n, e): List<&2, Shared.Bytes()>
        }
      {==}
    case Con{l, r}:
      %Equal.sym(
        List<&2, Shared.Bytes()>,
        Lines.apply(
          List.length(&2, Shared.Bytes(), r),
          Cut.left(Cut{r, o, n, e}),
          List.length(&2, Shared.Bytes(), o),
          n
        ),
        Cut.right(Cut{r, o, n, e}),
        Lines.apply_cut(r, o, n, e)
      ):
        {l <> _ == l <> Cut.right(Cut{r, o, n, e}): List<&2, Shared.Bytes()>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# the lines of b
def Lines.list.of(s: Shared.Bytes() & List<&2, Shared.Bytes()>) -> List<&2, Shared.Bytes()>:
  match s:
    case Tuple{l, ls}:
      l <> ls

# the lines of b, as a list
def Lines.list(b: Shared.Bytes()) -> List<&2, Shared.Bytes()>:
  Lines.list.of(Lines.split(b))

# the bytes of the lines ls
def Lines.bytes(ls: List<&2, Shared.Bytes()>) -> Shared.Bytes():
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      Lines.join(r, l)

# the bytes of a split are the bytes of its lines
def Lines.bytes_of(
  s: Shared.Bytes() & List<&2, Shared.Bytes()>
) -> {Lines.bytes(Lines.list.of(s)) == Lines.join.of(s): Shared.Bytes()}:
  match s:
    case Tuple{l, ls}:
      {==}

# the lines of b give back b
law Lines.bytes_list:
  for b: Shared.Bytes()
  {Lines.bytes(Lines.list(b)) == b: Shared.Bytes()}

def Lines.bytes_list(b):
  +b = b
  Equal.trans(
    Shared.Bytes(),
    Lines.bytes(Lines.list(b)),
    Lines.join.of(Lines.split(b)),
    b,
    Lines.bytes_of(Lines.split(b)),
    Lines.read_back(b)
  )

# Formats
# -------

# a change between two versions: Lines keeps the first keep lines, drops the
# next drop lines and puts the lines put in their place; Whole is the new
# content; Pieces is the new shape of an embedding, with a patch for each of
# its texts and each of its regions
type Patch is Data:
  Patch.lines{keep: Nat, drop: Nat, put: List<&2, Shared.Bytes()>}
  Patch.whole{bytes: Shared.Bytes()}
  Patch.pieces{shape: List<&2, Shape>, texts: List<&2, Patch>, regions: List<&2, Patch>}

# x is not 0
def Plain.not_nul(x: U32) -> Bool:
  Bool.not(U32.is_eq(x, 0))

# b is text: no byte of it is 0
def Plain.is_text(b: Shared.Bytes()) -> Bool:
  List.all(~&2, ~U32, ~Plain.not_nul, b)

# the patch of the lines of a cut
def Lines.patch(c: Cut) -> Patch:
  match c:
    case Cut{s, o, n, e}:
      Patch.lines{List.length(&2, Shared.Bytes(), s), List.length(&2, Shared.Bytes(), o), n}

# the patch from a to b, as lines when both are text (text)
def Plain.diff.by(text: Bool, a: Shared.Bytes(), b: Shared.Bytes()) -> Patch:
  match text:
    case True{}:
      Lines.patch(Lines.cut(Lines.list(a), Lines.list(b)))
    case False{}:
      Patch.whole{b}

# the patch from a to b
def Plain.diff(+a: Shared.Bytes(), +b: Shared.Bytes()) -> Patch:
  Plain.diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# a after the patch p; a patch of an embedding leaves a as it is
def Plain.apply(a: Shared.Bytes(), p: Patch) -> Shared.Bytes():
  match p:
    case Patch.lines{k, d, put}:
      Lines.bytes(Lines.apply(k, Lines.list(a), d, put))
    case Patch.whole{x}:
      x
    case Patch.pieces{sh, ts, rs}:
      a

# the patch of a cut c of the lines of a, applied to a, gives the bytes of the
# new lines lb of c
def Plain.apply_patch(
  c: Cut,
  a: Shared.Bytes(),
  lb: List<&2, Shared.Bytes()>,
  hl: {Cut.left(c) == Lines.list(a): List<&2, Shared.Bytes()>},
  hr: {Cut.right(c) == lb: List<&2, Shared.Bytes()>}
) -> {Plain.apply(a, Lines.patch(c)) == Lines.bytes(lb): Shared.Bytes()}:
  match c:
    case Cut{s, o, n, e}:
      Equal.cong(
        List<&2, Shared.Bytes()>,
        Shared.Bytes(),
        z => Lines.bytes(z),
        Lines.apply(List.length(&2, Shared.Bytes(), s), Lines.list(a), List.length(&2, Shared.Bytes(), o), n),
        lb,
        %hl: {Lines.apply(List.length(&2, Shared.Bytes(), s), _, List.length(&2, Shared.Bytes(), o), n) == lb: List<&2, Shared.Bytes()>}
        %hr: {Lines.apply(List.length(&2, Shared.Bytes(), s), Cut.left(Cut{s, o, n, e}), List.length(&2, Shared.Bytes(), o), n) == _: List<&2, Shared.Bytes()>}
        Lines.apply_cut(s, o, n, e))

# Plain.apply_diff, by whether both are text (text)
def Plain.apply_diff.by(
  text: Bool,
  +a: Shared.Bytes(),
  +b: Shared.Bytes()
) -> {Plain.apply(a, Plain.diff.by(text, a, b)) == b: Shared.Bytes()}:
  match text:
    case True{}:
      +la = Lines.list(a)
      +lb = Lines.list(b)
      Equal.trans(
        Shared.Bytes(),
        Plain.apply(a, Lines.patch(Lines.cut(la, lb))),
        Lines.bytes(lb),
        b,
        Plain.apply_patch(
          Lines.cut(la, lb),
          a,
          lb,
          Lines.cut_left(la, lb),
          Lines.cut_right(la, lb)
        ),
        Lines.bytes_list(b)
      )
    case False{}:
      {==}

# the patch from a to b, applied to a, gives b
law Plain.apply_diff:
  for +a: Shared.Bytes()
  for +b: Shared.Bytes()
  {Plain.apply(a, Plain.diff(a, b)) == b: Shared.Bytes()}

def Plain.apply_diff(a, b):
  Plain.apply_diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# Merges
# ------
# A merge of x and y, two changes of b. Before any format looks, Merge.decide
# takes the one change when only one side changed, or when both made the same
# change; so these merges hold for every format (Format.merge_*). A format
# merges only what both sides changed, differently. Plain text merges by
# lines: when the lines that one side changes end before the other's start,
# the merge makes the one change to the other side (Format.merge_apart).

# a merge: its bytes, or a clash
type Merged is Data:
  Merged.clean{bytes: Shared.Bytes()}
  Merged.clash{}

# the lines of the cut c changed in the lines ls: c's change made to ls
def Cut.apply(c: Cut, ls: List<&2, Shared.Bytes()>) -> List<&2, Shared.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      Lines.apply(List.length(&2, Shared.Bytes(), s), ls, List.length(&2, Shared.Bytes(), o), n)

# the lines that the cut cx changes end before the ones that cy changes start
def Plain.before(cx: Cut, cy: Cut) -> Bool:
  match cx cy:
    case Cut{sx, ox, nx, ex} Cut{sy, oy, ny, ey}:
      Nat.is_lt(
        Nat.add(List.length(&2, Shared.Bytes(), sx), List.length(&2, Shared.Bytes(), ox)),
        List.length(&2, Shared.Bytes(), sy)
      )

# the merge of the cuts cx and cy, once cx is known to end before cy starts
# (x_first) or cy before cx (y_first): one change made to the other's lines
def Plain.merge.order(x_first: Bool, y_first: Bool, cx: Cut, cy: Cut) -> Merged:
  match x_first y_first:
    case True{} w:
      Merged.clean{Lines.bytes(Cut.apply(cx, Cut.right(cy)))}
    case False{} True{}:
      Merged.clean{Lines.bytes(Cut.apply(cy, Cut.right(cx)))}
    case False{} False{}:
      Merged.clash{}

# the merge of two cuts of the same lines
def Plain.merge.cuts(+cx: Cut, +cy: Cut) -> Merged:
  Plain.merge.order(Plain.before(cx, cy), Plain.before(cy, cx), cx, cy)

# the merge of two text changes, by their lines
def Plain.merge.lines(b: Shared.Bytes(), x: Shared.Bytes(), y: Shared.Bytes()) -> Merged:
  +lb = Lines.list(b)
  Plain.merge.cuts(Lines.cut(lb, Lines.list(x)), Lines.cut(lb, Lines.list(y)))

# the merge of two different changes, as lines when all three are text (text)
def Plain.merge.text(text: Bool, b: Shared.Bytes(), x: Shared.Bytes(), y: Shared.Bytes()) -> Merged:
  match text:
    case True{}:
      Plain.merge.lines(b, x, y)
    case False{}:
      Merged.clash{}

# what a merge takes: y when x is b (theirs), x when y is b or x is y (ours),
# else both changes, piece by piece when they are an embedding of one shape
# (pieces)
type Decision is Data:
  Decision.theirs{}
  Decision.ours{}
  Decision.both{}
  Decision.pieces{}

# ours when x is y (held), else both
def Merge.decide.same(held: Bool) -> Decision:
  match held:
    case True{}:
      Decision.ours{}
    case False{}:
      Decision.both{}

# ours when y is b (held), else as x and y are the same or not
def Merge.decide.right(held: Bool, x: Shared.Bytes(), y: Shared.Bytes()) -> Decision:
  match held:
    case True{}:
      Decision.ours{}
    case False{}:
      Merge.decide.same(Shared.Bytes.is_eq(x, y))

# theirs when x is b (held), else as y is b or not
def Merge.decide.left(
  held: Bool,
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  +y: Shared.Bytes()
) -> Decision:
  match held:
    case True{}:
      Decision.theirs{}
    case False{}:
      Merge.decide.right(Shared.Bytes.is_eq(y, b), x, y)

# what a merge of x and y, two changes of b, takes before any format looks
def Merge.decide(+b: Shared.Bytes(), +x: Shared.Bytes(), y: Shared.Bytes()) -> Decision:
  Merge.decide.left(Shared.Bytes.is_eq(x, b), b, x, y)

# the change that the decision d takes of x and y, none for both
def Decision.take(d: Decision, x: Shared.Bytes(), y: Shared.Bytes()) -> Maybe<&2, Shared.Bytes()>:
  match d:
    case Decision.theirs{}:
      Some{y}
    case Decision.ours{}:
      Some{x}
    case Decision.both{}:
      None{}
    case Decision.pieces{}:
      None{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Merge.left_only once x is known to be b or not (held)
def Merge.left_only.at(
  held: Bool,
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  e: {Shared.Bytes.is_eq(x, b) == held: Bool}
) -> {Decision.take(Merge.decide.left(held, b, x, b), x, b) == Some{x}: Maybe<&2, Shared.Bytes()>}:
  match held:
    case True{}:
      %Equal.sym(
        Shared.Bytes(),
        x,
        b,
        Shared.Bytes.is_eq_sound(x, b)(e)
      ): {Some{b} == Some{_}: Maybe<&2, Shared.Bytes()>}
      {==}
    case False{}:
      %Equal.sym(Bool, Shared.Bytes.is_eq(b, b), True{}, Shared.Bytes.is_eq_refl(b)):
        {Decision.take(Merge.decide.right(_, x, b), x, b) == Some{x}: Maybe<&2, Shared.Bytes()>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# when only x changed b, the decision takes x
def Merge.left_only(
  +b: Shared.Bytes(),
  +x: Shared.Bytes()
) -> {Decision.take(Merge.decide(b, x, b), x, b) == Some{x}: Maybe<&2, Shared.Bytes()>}:
  Merge.left_only.at(Shared.Bytes.is_eq(x, b), b, x, {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# when only y changed b, the decision takes y
def Merge.right_only(
  b: Shared.Bytes(),
  y: Shared.Bytes()
) -> {Decision.take(Merge.decide(b, b, y), b, y) == Some{y}: Maybe<&2, Shared.Bytes()>}:
  %Equal.sym(Bool, Shared.Bytes.is_eq(b, b), True{}, Shared.Bytes.is_eq_refl(b)):
    {Decision.take(Merge.decide.left(_, b, b, y), b, y) == Some{y}: Maybe<&2, Shared.Bytes()>}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Merge.same once x is known to be b or not (held)
def Merge.same.at(
  held: Bool,
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  e: {Shared.Bytes.is_eq(x, b) == held: Bool}
) -> {Decision.take(Merge.decide.left(held, b, x, x), x, x) == Some{x}: Maybe<&2, Shared.Bytes()>}:
  match held:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Shared.Bytes.is_eq(x, b), False{}, e):
        {Decision.take(Merge.decide.right(_, x, x), x, x) == Some{x}: Maybe<&2, Shared.Bytes()>}
      %Equal.sym(Bool, Shared.Bytes.is_eq(x, x), True{}, Shared.Bytes.is_eq_refl(x)):
        {Decision.take(Merge.decide.same(_), x, x) == Some{x}: Maybe<&2, Shared.Bytes()>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# when both made the same change, the decision takes it
def Merge.same(
  +b: Shared.Bytes(),
  +x: Shared.Bytes()
) -> {Decision.take(Merge.decide(b, x, x), x, x) == Some{x}: Maybe<&2, Shared.Bytes()>}:
  Merge.same.at(Shared.Bytes.is_eq(x, b), b, x, {==})

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
  Piece.text{bytes: Shared.Bytes()}
  Piece.region{bytes: Shared.Bytes(), closed: Bool}

# what kind a piece is, without its bytes
type Shape is Data:
  Shape.text{}
  Shape.region{closed: Bool}

# where p first occurs in some bytes: the bytes before it, and after it
type Found is Data:
  Found{before: Shared.Bytes(), after: Shared.Bytes()}

# b starts with p
def Bytes.starts(p: Shared.Bytes(), b: Shared.Bytes()) -> Bool:
  match p b:
    case Nil{} w:
      True{}
    case Con{x, pr} Con{y, br}:
      List.all.if(u => Bytes.starts(pr, br), U32.is_eq(x, y))
    case Con{x, pr} Nil{}:
      False{}

# the place m of p in some bytes, after the byte x
def Found.put(x: U32, m: Maybe<&2, Found>) -> Maybe<&2, Found>:
  match m:
    case None{}:
      None{}
    case Some{Found{u, w}}:
      Some{Found{x <> u, w}}

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- List.length runs only at the hit, where the lazy search stops: once per search
# where p first occurs in b, if it does
def Bytes.find(+p: Shared.Bytes(), b: Shared.Bytes()) -> Maybe<&2, Found>:
  match b:
    case Nil{}:
      Bool.pick(Maybe<&2, Found>, List.is_empty(&2, U32, p), Some{Found{[], []}}, None{})
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Found>,
        Bytes.starts(p, x <> r),
        u => Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
        u => Found.put(x, Bytes.find(p, r))
      )
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# the pieces of b, f steps at most: looking for an opening marker op (opening),
# or for the closing marker cl of a region (not opening); m is where the marker
# looked for first occurs in b
def Embed.split.go(
  f: Nat,
  +op: Shared.Bytes(),
  +cl: Shared.Bytes(),
  b: Shared.Bytes(),
  opening: Bool,
  m: Maybe<&2, Found>
) -> List<&2, Piece>:
  match f opening m:
    case 0n True{} w:
      [Piece.text{b}]
    case 0n False{} w:
      [Piece.region{b, False{}}]
    case 1n+e True{} None{}:
      [Piece.text{b}]
    case 1n+e True{} Some{Found{u, +w}}:
      Piece.text{u} <> Embed.split.go(e, op, cl, w, False{}, Bytes.find(cl, w))
    case 1n+e False{} None{}:
      [Piece.region{b, False{}}]
    case 1n+e False{} Some{Found{u, +w}}:
      Piece.region{u, True{}} <> Embed.split.go(e, op, cl, w, True{}, Bytes.find(op, w))

# the pieces of b, between the markers op and cl
def Embed.split(+op: Shared.Bytes(), cl: Shared.Bytes(), +b: Shared.Bytes()) -> List<&2, Piece>:
  Embed.split.go(1n+List.length(&2, U32, b), op, cl, b, True{}, Bytes.find(op, b))

# the bytes of the pieces ps, with the markers op and cl around each region
def Embed.join(+op: Shared.Bytes(), +cl: Shared.Bytes(), ps: List<&2, Piece>) -> Shared.Bytes():
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      List.append(&2, U32, t, Embed.join(op, cl, r))
    case Con{Piece.region{c, True{}}, r}:
      List.append(
        &2,
        U32,
        op,
        List.append(&2, U32, c, List.append(&2, U32, cl, Embed.join(op, cl, r)))
      )
    case Con{Piece.region{c, False{}}, r}:
      List.append(&2, U32, op, List.append(&2, U32, c, Embed.join(op, cl, r)))

# the bytes before a found place
def Found.before(m: Maybe<&2, Found>) -> Shared.Bytes():
  match m:
    case Some{Found{u, w}}:
      u
    case None{}:
      []

# the bytes after a found place
def Found.after(m: Maybe<&2, Found>) -> Shared.Bytes():
  match m:
    case Some{Found{u, w}}:
      w
    case None{}:
      []

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bytes that start with p are p, then the rest
def Bytes.starts_drop(
  p: Shared.Bytes(),
  b: Shared.Bytes()
) -> {
  Bytes.starts(p, b) == True{}: Bool
} -> {b == List.append(&2, U32, p, List.drop(&2, U32, b, List.length(&2, U32, p))): Shared.Bytes()}:
  match p b:
    case Nil{} w:
      h => Equal.sym(
        Shared.Bytes(),
        List.drop(&2, U32, w, 0n),
        w,
        Shared.List.drop_zero(&2, U32, w)
      )
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
              ): Shared.Bytes()
          }
        %Bytes.starts_drop(
          pr,
          br
        )(Shared.List.all.if_rest(U32.is_eq(x, y), u => Bytes.starts(pr, br))(h)):
          {y <> br == y <> _: Shared.Bytes()}
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
            ): Shared.Bytes()
        },
        Shared.Bool.false_ne_true(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Bytes.find_cut at x <> r, by whether p starts there (hit)
def Bytes.find_cut.at(
  -u: Shared.Bytes(),
  -w: Shared.Bytes(),
  hit: Bool,
  p: Shared.Bytes(),
  x: U32,
  r: Shared.Bytes(),
  rest: Maybe<&2, Found>,
  eh: {Bytes.starts(p, x <> r) == hit: Bool},
  ih: @u2: Shared.Bytes() -> @w2: Shared.Bytes() -> {
    rest == Some{Found{u2, w2}}: Maybe<&2, Found>
  } -> {r == List.append(&2, U32, u2, List.append(&2, U32, p, w2)): Shared.Bytes()}
) -> {
  Shared.Bool.when(
    Maybe<&2, Found>,
    hit,
    z => Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
    z => Found.put(x, rest)
  )
    == Some{Found{u, w}}: Maybe<&2, Found>
} -> {x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Shared.Bytes()}:
  match hit rest:
    case True{} m:
      +h =>
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.before(z),
          Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
          Some{Found{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Shared.Bytes()}
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.after(z),
          Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}},
          Some{Found{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, p, _): Shared.Bytes()}
        Bytes.starts_drop(p, x <> r)(eh)
    case False{} None{}:
      h => Empty.absurd(
        {x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Shared.Bytes()},
        Shared.Maybe.none_ne_some(Found, Found{u, w}, h)
      )
    case False{} Some{Found{u2, w2}}:
      +h =>
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.before(z),
          Some{Found{x <> u2, w2}},
          Some{Found{u, w}},
          h
        ):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Shared.Bytes()}
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.after(z),
          Some{Found{x <> u2, w2}},
          Some{Found{u, w}},
          h
        ):
          {x <> r == x <> List.append(&2, U32, u2, List.append(&2, U32, p, _)): Shared.Bytes()}
        %ih(u2)(w2)({==}): {x <> r == x <> _: Shared.Bytes()}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# what Bytes.find finds cuts b: the bytes before, the pattern, the bytes after
def Bytes.find_cut(
  -u: Shared.Bytes(),
  -w: Shared.Bytes(),
  b: Shared.Bytes(),
  +p: Shared.Bytes()
) -> {
  Bytes.find(p, b) == Some{Found{u, w}}: Maybe<&2, Found>
} -> {b == List.append(&2, U32, u, List.append(&2, U32, p, w)): Shared.Bytes()}:
  match b p:
    case Nil{} Nil{}:
      +h =>
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.before(z),
          Some{Found{[], []}},
          Some{Found{u, w}},
          h
        ):
          {Nil{} == List.append(&2, U32, _, List.append(&2, U32, Nil{}, w)): Shared.Bytes()}
        %Equal.cong(
          Maybe<&2, Found>,
          Shared.Bytes(),
          z => Found.after(z),
          Some{Found{[], []}},
          Some{Found{u, w}},
          h
        ):
          {Nil{} == List.append(&2, U32, Nil{}, List.append(&2, U32, Nil{}, _)): Shared.Bytes()}
        {==}
    case Nil{} Con{y, q}:
      h => Empty.absurd(
        {Nil{} == List.append(&2, U32, u, List.append(&2, U32, y <> q, w)): Shared.Bytes()},
        Shared.Maybe.none_ne_some(Found, Found{u, w}, h)
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
def Embed.marker(opening: Bool, op: Shared.Bytes(), cl: Shared.Bytes()) -> Shared.Bytes():
  match opening:
    case True{}:
      op
    case False{}:
      cl

# the bytes that the pieces of a split stand for: b outside a region
# (opening), else the opening marker op, then b
def Embed.whole(opening: Bool, op: Shared.Bytes(), b: Shared.Bytes()) -> Shared.Bytes():
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
  +op: Shared.Bytes(),
  +cl: Shared.Bytes(),
  b: Shared.Bytes(),
  opening: Bool,
  m: Maybe<&2, Found>,
  hm: @u: Shared.Bytes() -> @w: Shared.Bytes() -> {
    m == Some{Found{u, w}}: Maybe<&2, Found>
  } -> {
    b
      == List.append(
        &2,
        U32,
        u,
        List.append(&2, U32, Embed.marker(opening, op, cl), w)
      ): Shared.Bytes()
  }
) -> {
  Embed.join(
    op,
    cl,
    Embed.split.go(f, op, cl, b, opening, m)
  )
    == Embed.whole(opening, op, b): Shared.Bytes()
}:
  match f opening m:
    case 0n True{} n:
      Shared.List.append_nil(U32, b)
    case 0n False{} n:
      Equal.cong(
        Shared.Bytes(),
        Shared.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, b, []),
        b,
        Shared.List.append_nil(U32, b)
      )
    case 1n+e True{} None{}:
      Shared.List.append_nil(U32, b)
    case 1n+e True{} Some{Found{u, +w}}:
      %Equal.sym(
        Shared.Bytes(),
        Embed.join(op, cl, Embed.split.go(e, op, cl, w, False{}, Bytes.find(cl, w))),
        List.append(&2, U32, op, w),
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
        {List.append(&2, U32, u, _) == b: Shared.Bytes()}
      Equal.sym(
        Shared.Bytes(),
        b,
        List.append(&2, U32, u, List.append(&2, U32, op, w)),
        hm(u)(w)({==})
      )
    case 1n+e False{} None{}:
      Equal.cong(
        Shared.Bytes(),
        Shared.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, b, []),
        b,
        Shared.List.append_nil(U32, b)
      )
    case 1n+e False{} Some{Found{u, +w}}:
      %Equal.sym(
        Shared.Bytes(),
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
            == List.append(&2, U32, op, b): Shared.Bytes()
        }
      Equal.cong(
        Shared.Bytes(),
        Shared.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, u, List.append(&2, U32, cl, w)),
        b,
        Equal.sym(
          Shared.Bytes(),
          b,
          List.append(&2, U32, u, List.append(&2, U32, cl, w)),
          hm(u)(w)({==})
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the pieces of b, joined, give back b: an embedding loses nothing
law Embed.join_split:
  for +op: Shared.Bytes()
  for +cl: Shared.Bytes()
  for +b: Shared.Bytes()
  {Embed.join(op, cl, Embed.split(op, cl, b)) == b: Shared.Bytes()}

def Embed.join_split(op, cl, b):
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
    case Piece.text{t}:
      Shape.text{}
    case Piece.region{c, k}:
      Shape.region{k}

# the shapes of the pieces ps
def Pieces.shape(ps: List<&2, Piece>) -> List<&2, Shape>:
  match ps:
    case Nil{}:
      []
    case Con{p, r}:
      Piece.shape(p) <> Pieces.shape(r)

# the bytes of the text pieces of ps, in order
def Pieces.texts(ps: List<&2, Piece>) -> List<&2, Shared.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      t <> Pieces.texts(r)
    case Con{Piece.region{c, k}, r}:
      Pieces.texts(r)

# the bytes of the regions of ps, in order
def Pieces.regions(ps: List<&2, Piece>) -> List<&2, Shared.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      Pieces.regions(r)
    case Con{Piece.region{c, k}, r}:
      c <> Pieces.regions(r)

# the pieces of the shapes sh, filled with the texts ts and the regions rs in
# order; a missing one is empty
def Pieces.build(
  sh: List<&2, Shape>,
  ts: List<&2, Shared.Bytes()>,
  rs: List<&2, Shared.Bytes()>
) -> List<&2, Piece>:
  match sh ts rs:
    case Nil{} t r:
      []
    case Con{Shape.text{}, sr} Nil{} r:
      Piece.text{[]} <> Pieces.build(sr, [], r)
    case Con{Shape.text{}, sr} Con{t, tr} r:
      Piece.text{t} <> Pieces.build(sr, tr, r)
    case Con{Shape.region{k}, sr} t Nil{}:
      Piece.region{[], k} <> Pieces.build(sr, t, [])
    case Con{Shape.region{k}, sr} t Con{c, rr}:
      Piece.region{c, k} <> Pieces.build(sr, t, rr)

# the pieces of their own shape, texts and regions are the pieces
def Pieces.build_of(
  ps: List<&2, Piece>
) -> {Pieces.build(Pieces.shape(ps), Pieces.texts(ps), Pieces.regions(ps)) == ps: List<&2, Piece>}:
  match ps:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Piece.text{bytes}:
          %Equal.sym(
            List<&2, Piece>,
            Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)),
            tail,
            Pieces.build_of(tail)
          ):
            {Piece.text{bytes} <> _ == Piece.text{bytes} <> tail: List<&2, Piece>}
          {==}
        case Piece.region{bytes1, closed}:
          %Equal.sym(
            List<&2, Piece>,
            Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)),
            tail,
            Pieces.build_of(tail)
          ):
            {
              Piece.region{
                bytes1,
                closed
              }
                <> _
                == Piece.region{bytes1, closed}
                <> tail: List<&2, Piece>
            }
          {==}

# Changes
# -------
# What a patch does, part by part, for a reader.

# a part of a resource: its kind (line, content), where it is (a line counts
# from 1; a whole content is at 0), and its bytes
type Item is Data:
  Item{kind: String, place: Nat, bytes: Shared.Bytes()}

# a part that a patch added or removed
type Change is Data:
  Change.added{item: Item}
  Change.removed{item: Item}

# the lines ls as the changes that make (c), counted from the line at
def Lines.changes(
  ~make: Item -> Change,
  ls: List<&2, Shared.Bytes()>,
  +at: Nat
) -> List<&2, Change>:
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      make(Item{"line", at, l}) <> Lines.changes(~make, r, 1n+at)

# the changes of a whole content from a to b, none when they are the same
# (held)
def Plain.changes.whole(held: Bool, a: Shared.Bytes(), b: Shared.Bytes()) -> List<&2, Change>:
  match held:
    case True{}:
      []
    case False{}:
      [Change.removed{Item{"content", 0n, a}}, Change.added{Item{"content", 0n, b}}]

# the changes of the patch p of a
def Plain.changes.of(+a: Shared.Bytes(), p: Patch) -> List<&2, Change>:
  match p:
    case Patch.lines{+k, d, put}:
      List.append(
        &2,
        Change,
        Lines.changes(
          ~(i => Change.removed{i}),
          List.take(&2, Shared.Bytes(), List.drop(&2, Shared.Bytes(), Lines.list(a), k), d),
          1n+k
        ),
        Lines.changes(~(i => Change.added{i}), put, 1n+k)
      )
    case Patch.whole{+x}:
      Plain.changes.whole(Shared.Bytes.is_eq(a, x), a, x)
    case Patch.pieces{sh, ts, rs}:
      []

# what changed from a to b, part by part
def Plain.changes(+a: Shared.Bytes(), b: Shared.Bytes()) -> List<&2, Change>:
  Plain.changes.of(a, Plain.diff(a, b))

# Imports
# -------
# A language names what a resource uses on lines of its own: an import, an
# include. Its rule says how to read those lines, and the conditions that each
# one sits under, so a conditional import is an edge with its conditions, and a
# qualified one keeps its alias.

# a line that starts with start, after blanks, names a target after the
# marker open, up to the marker close or the line's end, and after the marker
# alias the name that it gets; a line that starts with when opens a
# condition, otherwise flips it, end closes it. An empty marker never starts a
# line; an empty open or close is the place right after start or the line's
# end.
type Rule is Data:
  Rule{
    start: Shared.Bytes(),
    open: Shared.Bytes(),
    close: Shared.Bytes(),
    alias: Shared.Bytes(),
    when: Shared.Bytes(),
    otherwise: Shared.Bytes(),
    end: Shared.Bytes()
  }

# a condition that an edge sits under: its line, and whether the edge is in
# its first part (holds) or after otherwise
type Cond is Data:
  Cond{test: Shared.Bytes(), holds: Bool}

# what a resource uses: the target as written, the name that it gets (empty
# without one), and the conditions that it sits under, innermost first
type Edge is Data:
  Edge{target: Shared.Bytes(), alias: Shared.Bytes(), conds: List<&2, Cond>}

# x is a space or a tab
def Line.is_blank(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9))

# l without its leading blanks
def Line.trim(l: Shared.Bytes()) -> Shared.Bytes():
  match l:
    case Nil{}:
      []
    case Con{+x, +r}:
      Shared.Bool.when(Shared.Bytes(), Line.is_blank(x), u => Line.trim(r), u => x <> r)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- Bytes.starts of an empty marker returns at once
# l starts with the marker p, which is not empty
def Line.marks(+p: Shared.Bytes(), l: Shared.Bytes()) -> Bool:
  Bool.and(Bool.not(List.is_empty(&2, U32, p)), Bytes.starts(p, l))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# x cut where the marker m was found, when it is not empty (held): all of x
# comes before it when it is empty or not in x
def Rule.cut.of(held: Bool, m: Maybe<&2, Found>, x: Shared.Bytes()) -> Found:
  match held m:
    case True{} Some{f}:
      f
    case h n:
      Found{x, []}

# x cut at the first marker p
def Rule.cut(+p: Shared.Bytes(), +x: Shared.Bytes()) -> Found:
  Rule.cut.of(Bool.not(List.is_empty(&2, U32, p)), Bytes.find(p, x), x)

# the bytes after a cut
def Found.rest(c: Found) -> Shared.Bytes():
  match c:
    case Found{u, w}:
      w

# the edge whose target and what follows it are cut at the close marker (c),
# with the alias marker al, under the conditions cs
def Rule.named(c: Found, al: Shared.Bytes(), cs: List<&2, Cond>) -> Edge:
  match c:
    case Found{t, w}:
      Edge{t, Found.rest(Rule.cut(al, w)), cs}

# the edges of the bytes w after a start marker, once the open marker is
# known to be empty or not (held), and m is where it first occurs in w
def Rule.opened(
  held: Bool,
  m: Maybe<&2, Found>,
  w: Shared.Bytes(),
  cl: Shared.Bytes(),
  al: Shared.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match held m:
    case False{} n:
      [Rule.named(Rule.cut(cl, w), al, cs)]
    case True{} None{}:
      []
    case True{} Some{Found{u, a}}:
      [Rule.named(Rule.cut(cl, a), al, cs)]

# the edges of the trimmed line t, once it is known to start with the start
# marker st or not (started)
def Rule.line.at(
  started: Bool,
  st: Shared.Bytes(),
  t: Shared.Bytes(),
  +op: Shared.Bytes(),
  cl: Shared.Bytes(),
  al: Shared.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match started:
    case True{}:
      +w = List.drop(&2, U32, t, List.length(&2, U32, st))
      Rule.opened(Bool.not(List.is_empty(&2, U32, op)), Bytes.find(op, w), w, cl, al, cs)
    case False{}:
      []

# the edges that the line l names under the conditions cs: one or none
def Rule.line(r: Rule, l: Shared.Bytes(), cs: List<&2, Cond>) -> List<&2, Edge>:
  match r:
    case Rule{+st, op, cl, al, wh, ot, en}:
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
  t: Shared.Bytes(),
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
def Rule.step(r: Rule, l: Shared.Bytes(), cs: List<&2, Cond>) -> List<&2, Cond>:
  match r:
    case Rule{st, op, cl, al, wh, ot, en}:
      +t = Line.trim(l)
      Rule.step.at(Line.marks(en, t), Line.marks(ot, t), Line.marks(wh, t), t, cs)

# the edges of the lines ls under the conditions cs
def Rule.edges.go(ls: List<&2, Shared.Bytes()>, +r: Rule, +cs: List<&2, Cond>) -> List<&2, Edge>:
  match ls:
    case Nil{}:
      []
    case Con{+l, rest}:
      List.append(&2, Edge, Rule.line(r, l, cs), Rule.edges.go(rest, r, Rule.step(r, l, cs)))

# the edges of the bytes b
def Rule.edges(r: Rule, b: Shared.Bytes()) -> List<&2, Edge>:
  Rule.edges.go(Lines.list(b), r, [])

# Nested formats
# --------------
# A format is a leaf, an embedding of an inner format in an outer one, or a
# language: a base format and the rule of its imports. Formats nest to any
# depth (CSS and JS inside HTML), and the laws below hold for every one. Each
# operation takes a list of items, so that an embedding hands all its texts to
# the outer format and all its regions to the inner one in one call; an old
# item that is missing is empty.
type Format is Data:
  Format.leaf{kind: Leaf}
  Format.embed{outer: Format, open: Shared.Bytes(), close: Shared.Bytes(), inner: Format}
  Format.code{base: Format, rule: Rule}

# a format that holds no other: lines (the default), the content as one whole
# part, or a submodule, a pointer to a child that the core reads and merges
type Leaf is Data:
  Leaf.lines{}
  Leaf.whole{}
  Leaf.module{}

# the first of the items xs, empty when there is none
def Items.first(xs: List<&2, Shared.Bytes()>) -> Shared.Bytes():
  Maybe.default(&2, Shared.Bytes(), List.head(&2, Shared.Bytes(), xs), [])

# the patch from a to b, in the leaf k
def Leaf.diff(k: Leaf, a: Shared.Bytes(), b: Shared.Bytes()) -> Patch:
  match k:
    case Leaf.lines{}:
      Plain.diff(a, b)
    case Leaf.whole{}:
      Patch.whole{b}
    case Leaf.module{}:
      Patch.whole{b}

# the patch from a to b, in the leaf k, applied to a, gives b
def Leaf.apply_diff(
  k: Leaf,
  a: Shared.Bytes(),
  b: Shared.Bytes()
) -> {Plain.apply(a, Leaf.diff(k, a, b)) == b: Shared.Bytes()}:
  match k:
    case Leaf.lines{}:
      Plain.apply_diff(a, b)
    case Leaf.whole{}:
      {==}
    case Leaf.module{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the patches from the items as to the items bs, one for each of bs
def Format.diffs(
  f: Format,
  bs: List<&2, Shared.Bytes()>,
  +as: List<&2, Shared.Bytes()>
) -> List<&2, Patch>:
  match f bs:
    case Format.leaf{k} Nil{}:
      []
    case Format.leaf{+k} Con{b, br}:
      Leaf.diff(
        k,
        Items.first(as),
        b
      )
        <> Format.diffs(Format.leaf{k}, br, List.tail(&2, Shared.Bytes(), as))
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{b, br}:
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
      ) Format.diffs(Format.embed{o, op, cl, i}, br, List.tail(&2, Shared.Bytes(), as))
      Patch.pieces{Pieces.shape(pb), ts, rs} <> rest
    case Format.code{base, r} c:
      Format.diffs(base, c, as)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the items as after the patches ps, one for each of ps; a patch of another
# format applies as plain
def Format.applies(
  f: Format,
  ps: List<&2, Patch>,
  +as: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  match f ps:
    case Format.leaf{k} Nil{}:
      []
    case Format.leaf{+k} Con{p, pr}:
      Plain.apply(
        Items.first(as),
        p
      )
        <> Format.applies(Format.leaf{k}, pr, List.tail(&2, Shared.Bytes(), as))
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{Patch.pieces{sh, tps, rps}, pr}:
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
      ) Format.applies(Format.embed{o, op, cl, i}, pr, List.tail(&2, Shared.Bytes(), as))
      Embed.join(op, cl, Pieces.build(sh, ts, rs)) <> rest
    case Format.embed{+o, +op, +cl, +i} Con{p, pr}:
      Plain.apply(
        Items.first(as),
        p
      )
        <> Format.applies(Format.embed{o, op, cl, i}, pr, List.tail(&2, Shared.Bytes(), as))
    case Format.code{base, r} q:
      Format.applies(base, q, as)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# the patches from as to bs, applied to as, give bs, in every format
law Format.apply_diffs:
  for f: Format
  for +bs: List<&2, Shared.Bytes()>
  for +as: List<&2, Shared.Bytes()>
  {Format.applies(f, Format.diffs(f, bs, as), as) == bs: List<&2, Shared.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Format.apply_diffs(f, bs, as):
  match f bs:
    case Format.leaf{k} Nil{}:
      {==}
    case Format.leaf{+k} Con{b, br}:
      Shared.List.cons_eq(
        Shared.Bytes(),
        Plain.apply(Items.first(as), Leaf.diff(k, Items.first(as), b)),
        b,
        Format.applies(
          Format.leaf{k},
          Format.diffs(Format.leaf{k}, br, List.tail(&2, Shared.Bytes(), as)),
          List.tail(&2, Shared.Bytes(), as)
        ),
        br,
        Leaf.apply_diff(k, Items.first(as), b),
        Format.apply_diffs(Format.leaf{k}, br, List.tail(&2, Shared.Bytes(), as))
      )
    case Format.embed{o, op, cl, i} Nil{}:
      {==}
    case Format.embed{+o, +op, +cl, +i} Con{+b, br}:
      +pa = Embed.split(op, cl, Items.first(as))
      +pb = Embed.split(op, cl, b)
      ta = Pieces.texts(pa)
      ra = Pieces.regions(pa)
      tb = Pieces.texts(pb)
      rb = Pieces.regions(pb)
      rest = List.tail(&2, Shared.Bytes(), as)
      Shared.List.cons_eq(
        Shared.Bytes(),
        Embed.join(op, cl, Pieces.build(Pieces.shape(pb), Format.applies(o, Format.diffs(o, tb, ta), ta), Format.applies(i, Format.diffs(i, rb, ra), ra))),
        b,
        Format.applies(Format.embed{o, op, cl, i}, Format.diffs(Format.embed{o, op, cl, i}, br, rest), rest),
        br,
        %Equal.sym(List<&2, Shared.Bytes()>, Format.applies(o, Format.diffs(o, tb, ta), ta), tb, Format.apply_diffs(o, tb, ta)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), _, Format.applies(i, Format.diffs(i, rb, ra), ra))) == b: Shared.Bytes()}
        %Equal.sym(List<&2, Shared.Bytes()>, Format.applies(i, Format.diffs(i, rb, ra), ra), rb, Format.apply_diffs(i, rb, ra)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), tb, _)) == b: Shared.Bytes()}
        %Equal.sym(List<&2, Piece>, Pieces.build(Pieces.shape(pb), tb, rb), pb, Pieces.build_of(pb)):
          {Embed.join(op, cl, _) == b: Shared.Bytes()}
        Embed.join_split(op, cl, b),
        Format.apply_diffs(Format.embed{o, op, cl, i}, br, rest))
    case Format.code{base, r} c:
      Format.apply_diffs(base, c, as)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Nested merges
# -------------

# a and b are the same kind of piece
def Shape.same(a: Shape, b: Shape) -> Bool:
  match a b:
    case Shape.text{} Shape.text{}:
      True{}
    case Shape.region{True{}} Shape.region{True{}}:
      True{}
    case Shape.region{False{}} Shape.region{False{}}:
      True{}
    case _ _:
      False{}

# the shape of the pieces of b, between the markers op and cl
def Embed.shape(op: Shared.Bytes(), cl: Shared.Bytes(), b: Shared.Bytes()) -> List<&2, Shape>:
  Pieces.shape(Embed.split(op, cl, b))

# what to take when both changes differ, in the format f
def Format.decide.both(
  f: Format,
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes()
) -> Decision:
  match f:
    case Format.leaf{k}:
      Decision.both{}
    case Format.embed{o, +op, +cl, i}:
      +sb = Embed.shape(op, cl, b)
      Bool.pick(
        Decision,
        List.all.if(
          u => Shared.List.same(~Shape, ~Shape.same, sb, Embed.shape(op, cl, y)),
          Shared.List.same(~Shape, ~Shape.same, sb, Embed.shape(op, cl, x))
        ),
        Decision.pieces{},
        Decision.both{}
      )
    case Format.code{base, r}:
      Format.decide.both(base, b, x, y)

# the decision d, in the format f
def Format.decide.on(
  d: Decision,
  f: Format,
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes()
) -> Decision:
  match d:
    case Decision.both{}:
      Format.decide.both(f, b, x, y)
    case e:
      e

# what a merge of x and y, two changes of b, takes in the format f
def Format.decide(
  f: Format,
  +b: Shared.Bytes(),
  +x: Shared.Bytes(),
  +y: Shared.Bytes()
) -> Decision:
  Format.decide.on(Merge.decide(b, x, y), f, b, x, y)

# a merge to make: the base, the two changes, and what to take
type Job is Data:
  Job{base: Shared.Bytes(), ours: Shared.Bytes(), theirs: Shared.Bytes(), decision: Decision}

# the job of merging x and y, two changes of b, in the format f
def Job.of(f: Format, +b: Shared.Bytes(), +x: Shared.Bytes(), +y: Shared.Bytes()) -> Job:
  Job{b, x, y, Format.decide(f, b, x, y)}

# the jobs of the items bs, xs and ys, place by place, in the format f
def Jobs.of(
  bs: List<&2, Shared.Bytes()>,
  +f: Format,
  +xs: List<&2, Shared.Bytes()>,
  +ys: List<&2, Shared.Bytes()>
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
        <> Jobs.of(br, f, List.tail(&2, Shared.Bytes(), xs), List.tail(&2, Shared.Bytes(), ys))

# the change that the decision d takes of x and y, a clash for both
def Merge.taken(d: Decision, x: Shared.Bytes(), y: Shared.Bytes()) -> Merged:
  match d:
    case Decision.theirs{}:
      Merged.clean{y}
    case Decision.ours{}:
      Merged.clean{x}
    case e:
      Merged.clash{}

# the merge of x and y, two changes of b, by lines, with the decision d
def Merge.plain(d: Decision, +b: Shared.Bytes(), +x: Shared.Bytes(), +y: Shared.Bytes()) -> Merged:
  match d:
    case Decision.theirs{}:
      Merged.clean{y}
    case Decision.ours{}:
      Merged.clean{x}
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
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes()
) -> Merged:
  match k:
    case Leaf.lines{}:
      Merge.plain(d, b, x, y)
    case Leaf.whole{}:
      Merge.taken(d, x, y)
    case Leaf.module{}:
      Merge.taken(d, x, y)

# the bytes x put before the bytes of a clean list m
def Merged.put(
  x: Shared.Bytes(),
  m: Maybe<&2, List<&2, Shared.Bytes()>>
) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# the bytes of the merges ms, when none clashes
def Merged.all(ms: List<&2, Merged>) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  match ms:
    case Nil{}:
      Some{[]}
    case Con{Merged.clean{x}, r}:
      Merged.put(x, Merged.all(r))
    case Con{Merged.clash{}, r}:
      None{}

# the embedding of the shape sh, with the merged texts mt and regions mr
def Merge.pieces(
  op: Shared.Bytes(),
  cl: Shared.Bytes(),
  sh: List<&2, Shape>,
  mt: Maybe<&2, List<&2, Shared.Bytes()>>,
  mr: Maybe<&2, List<&2, Shared.Bytes()>>
) -> Merged:
  match mt mr:
    case Some{ts} Some{rs}:
      Merged.clean{Embed.join(op, cl, Pieces.build(sh, ts, rs))}
    case _ _:
      Merged.clash{}

# the first merge of ms, a clash when there is none
def Merged.head(ms: List<&2, Merged>) -> Merged:
  match ms:
    case Nil{}:
      Merged.clash{}
    case Con{m, r}:
      m

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# the merges of the jobs js, in the format f. An embedding of one shape merges
# its texts in the outer format and its regions in the inner one; of other
# shapes, it merges as the outer format.
def Format.merges(f: Format, js: List<&2, Job>) -> List<&2, Merged>:
  match f js:
    case Format.leaf{k} Nil{}:
      []
    case Format.leaf{+k} Con{Job{b, x, y, d}, jr}:
      Leaf.merge(k, d, b, x, y) <> Format.merges(Format.leaf{k}, jr)
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{Job{b, x, y, Decision.pieces{}}, jr}:
      +pb = Embed.split(op, cl, b)
      +px = Embed.split(op, cl, x)
      +py = Embed.split(op, cl, y)
      jt = Jobs.of(Pieces.texts(pb), o, Pieces.texts(px), Pieces.texts(py))
      jr2 = Jobs.of(Pieces.regions(pb), i, Pieces.regions(px), Pieces.regions(py))
      mt mr rest = Format.merges(
        o,
        jt
      ) Format.merges(i, jr2) Format.merges(Format.embed{o, op, cl, i}, jr)
      Merge.pieces(op, cl, Pieces.shape(pb), Merged.all(mt), Merged.all(mr)) <> rest
    case Format.embed{+o, +op, +cl, +i} Con{Job{+b, +x, +y, Decision.both{}}, jr}:
      m rest = Format.merges(o, [Job.of(o, b, x, y)]) Format.merges(Format.embed{o, op, cl, i}, jr)
      Merged.head(m) <> rest
    case Format.embed{+o, +op, +cl, +i} Con{Job{b, x, y, d}, jr}:
      Merge.taken(d, x, y) <> Format.merges(Format.embed{o, op, cl, i}, jr)
    case Format.code{base, r} q:
      Format.merges(base, q)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# the merge of x and y, two changes of b, in the format f
def Format.merge(+f: Format, b: Shared.Bytes(), x: Shared.Bytes(), y: Shared.Bytes()) -> Merged:
  Merged.head(Format.merges(f, [Job.of(f, b, x, y)]))

# a decision that takes z of the changes merges to z, by lines
def Merge.plain_taken(
  d: Decision,
  -b: Shared.Bytes(),
  -x: Shared.Bytes(),
  -y: Shared.Bytes(),
  -z: Shared.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Merge.plain(d, b, x, y) == Merged.clean{z}: Merged}:
  match d:
    case Decision.theirs{}:
      %Equal.sym(
        Shared.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), y, z, h)
      ): {Merged.clean{_} == Merged.clean{z}: Merged}
      {==}
    case Decision.ours{}:
      %Equal.sym(
        Shared.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), x, z, h)
      ): {Merged.clean{_} == Merged.clean{z}: Merged}
      {==}
    case Decision.both{}:
      Empty.absurd(
        {Merge.plain(Decision.both{}, b, x, y) == Merged.clean{z}: Merged},
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )
    case Decision.pieces{}:
      Empty.absurd(
        {Merge.plain(Decision.pieces{}, b, x, y) == Merged.clean{z}: Merged},
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )

# a decision that takes z of the changes takes z
def Merge.taken_taken(
  d: Decision,
  -x: Shared.Bytes(),
  -y: Shared.Bytes(),
  -z: Shared.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Merge.taken(d, x, y) == Merged.clean{z}: Merged}:
  match d:
    case Decision.theirs{}:
      %Equal.sym(
        Shared.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), y, z, h)
      ): {Merged.clean{_} == Merged.clean{z}: Merged}
      {==}
    case Decision.ours{}:
      %Equal.sym(
        Shared.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), x, z, h)
      ): {Merged.clean{_} == Merged.clean{z}: Merged}
      {==}
    case Decision.both{}:
      Empty.absurd(
        {Merge.taken(Decision.both{}, x, y) == Merged.clean{z}: Merged},
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )
    case Decision.pieces{}:
      Empty.absurd(
        {Merge.taken(Decision.pieces{}, x, y) == Merged.clean{z}: Merged},
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )

# a decision that takes z of the changes merges to z, in every leaf
def Leaf.merge_taken(
  k: Leaf,
  -b: Shared.Bytes(),
  -x: Shared.Bytes(),
  -y: Shared.Bytes(),
  -z: Shared.Bytes(),
  d: Decision,
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Leaf.merge(k, d, b, x, y) == Merged.clean{z}: Merged}:
  match k:
    case Leaf.lines{}:
      Merge.plain_taken(d, b, x, y, z, h)
    case Leaf.whole{}:
      Merge.taken_taken(d, x, y, z, h)
    case Leaf.module{}:
      Merge.taken_taken(d, x, y, z, h)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a job whose decision takes z of its changes merges to z, in every format
def Format.merges_taken(
  f: Format,
  -b: Shared.Bytes(),
  -x: Shared.Bytes(),
  -y: Shared.Bytes(),
  -z: Shared.Bytes(),
  d: Decision,
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Format.merges(f, [Job{b, x, y, d}]) == [Merged.clean{z}]: List<&2, Merged>}:
  match f d:
    case Format.leaf{k} e:
      Equal.cong(
        Merged,
        List<&2, Merged>,
        m => [m],
        Leaf.merge(k, e, b, x, y),
        Merged.clean{z},
        Leaf.merge_taken(k, b, x, y, z, e, h)
      )
    case Format.embed{o, op, cl, i} Decision.theirs{}:
      %Equal.sym(
        Shared.Bytes(),
        y,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), y, z, h)
      ): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.embed{o, op, cl, i} Decision.ours{}:
      %Equal.sym(
        Shared.Bytes(),
        x,
        z,
        Shared.Maybe.some_inj(Shared.Bytes(), x, z, h)
      ): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.embed{o, op, cl, i} Decision.both{}:
      Empty.absurd(
        {
          Format.merges(
            Format.embed{o, op, cl, i},
            [Job{b, x, y, Decision.both{}}]
          )
            == [Merged.clean{z}]: List<&2, Merged>
        },
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )
    case Format.embed{o, op, cl, i} Decision.pieces{}:
      Empty.absurd(
        {
          Format.merges(
            Format.embed{o, op, cl, i},
            [Job{b, x, y, Decision.pieces{}}]
          )
            == [Merged.clean{z}]: List<&2, Merged>
        },
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )
    case Format.code{base, r} e:
      Format.merges_taken(base, b, x, y, z, e, h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a decision that takes z of the changes takes it in every format
def Format.decide.on_taken(
  d: Decision,
  -f: Format,
  -b: Shared.Bytes(),
  -x: Shared.Bytes(),
  -y: Shared.Bytes(),
  -z: Shared.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Decision.take(Format.decide.on(d, f, b, x, y), x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}:
  match d:
    case Decision.theirs{}:
      h
    case Decision.ours{}:
      h
    case Decision.both{}:
      Empty.absurd(
        {
          Decision.take(
            Format.decide.on(Decision.both{}, f, b, x, y),
            x,
            y
          )
            == Some{z}: Maybe<&2, Shared.Bytes()>
        },
        Shared.Maybe.none_ne_some(Shared.Bytes(), z, h)
      )
    case Decision.pieces{}:
      h

# the merge of a job whose base decision takes z is z, in every format
def Format.merge_taken(
  +f: Format,
  +b: Shared.Bytes(),
  +x: Shared.Bytes(),
  +y: Shared.Bytes(),
  -z: Shared.Bytes(),
  h: {Decision.take(Merge.decide(b, x, y), x, y) == Some{z}: Maybe<&2, Shared.Bytes()>}
) -> {Format.merge(f, b, x, y) == Merged.clean{z}: Merged}:
  Equal.cong(
    List<&2, Merged>,
    Merged,
    ms => Merged.head(ms),
    Format.merges(f, [Job.of(f, b, x, y)]),
    [Merged.clean{z}],
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

# when only x changed b, a merge takes x, in every format
law Format.merge_left_only:
  for +f: Format
  for +b: Shared.Bytes()
  for +x: Shared.Bytes()
  {Format.merge(f, b, x, b) == Merged.clean{x}: Merged}

def Format.merge_left_only(f, b, x):
  Format.merge_taken(f, b, x, b, x, Merge.left_only(b, x))

# when only y changed b, a merge takes y, in every format
law Format.merge_right_only:
  for +f: Format
  for +b: Shared.Bytes()
  for +y: Shared.Bytes()
  {Format.merge(f, b, b, y) == Merged.clean{y}: Merged}

def Format.merge_right_only(f, b, y):
  Format.merge_taken(f, b, b, y, y, Merge.right_only(b, y))

# when both made the same change, a merge takes it, in every format
law Format.merge_same:
  for +f: Format
  for +b: Shared.Bytes()
  for +x: Shared.Bytes()
  {Format.merge(f, b, x, x) == Merged.clean{x}: Merged}

def Format.merge_same(f, b, x):
  Format.merge_taken(f, b, x, x, x, Merge.same(b, x))

# What a format reads
# -------------------

# what changed from a to b, part by part, as the format f shows it to a
# reader: an embedding shows the changes of its outer format, over all of it
def Format.changes(f: Format, +a: Shared.Bytes(), +b: Shared.Bytes()) -> List<&2, Change>:
  match f:
    case Format.leaf{Leaf.lines{}}:
      Plain.changes(a, b)
    case Format.leaf{k}:
      Plain.changes.whole(Shared.Bytes.is_eq(a, b), a, b)
    case Format.embed{o, op, cl, i}:
      Format.changes(o, a, b)
    case Format.code{base, r}:
      Format.changes(base, a, b)

# the edges of each of the items bs, by the rule r
def Rule.edges.of(bs: List<&2, Shared.Bytes()>, +r: Rule) -> List<&2, Edge>:
  match bs:
    case Nil{}:
      []
    case Con{b, br}:
      List.append(&2, Edge, Rule.edges(r, b), Rule.edges.of(br, r))

# the texts (texts) or the regions of each of the items bs, between the
# markers op and cl
def Embed.parts(
  bs: List<&2, Shared.Bytes()>,
  texts: Bool,
  +op: Shared.Bytes(),
  +cl: Shared.Bytes()
) -> List<&2, Shared.Bytes()>:
  match bs texts:
    case Nil{} t:
      []
    case Con{b, br} True{}:
      List.append(
        &2,
        Shared.Bytes(),
        Pieces.texts(Embed.split(op, cl, b)),
        Embed.parts(br, True{}, op, cl)
      )
    case Con{b, br} False{}:
      List.append(
        &2,
        Shared.Bytes(),
        Pieces.regions(Embed.split(op, cl, b)),
        Embed.parts(br, False{}, op, cl)
      )

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- these walks cover the few pieces of one item; a tail walk would need a reverse that Pieces.build_of would then undo
# what the items bs use, in the format f: the edges of each language, in the
# parts that it reads
def Format.uses(f: Format, +bs: List<&2, Shared.Bytes()>) -> List<&2, Edge>:
  match f:
    case Format.leaf{k}:
      []
    case Format.embed{o, +op, +cl, i}:
      tp = Embed.parts(bs, True{}, op, cl)
      rp = Embed.parts(bs, False{}, op, cl)
      ts rs = Format.uses(o, tp) Format.uses(i, rp)
      List.append(&2, Edge, ts, rs)
    case Format.code{base, r}:
      List.append(&2, Edge, Rule.edges.of(bs, r), Format.uses(base, bs))
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# Known formats
# -------------

# a language whose imports name a target after start, up to close
def Format.imports(start: String, open: String, close: String, alias: String) -> Format:
  Format.code{
    Format.leaf{Leaf.lines{}},
    Rule{
      Shared.Bytes.of_text(start),
      Shared.Bytes.of_text(open),
      Shared.Bytes.of_text(close),
      Shared.Bytes.of_text(alias),
      [],
      [],
      []
    }
  }

# the format of the paths that end with a suffix
type Known is Data:
  Known{suffix: String, format: Format}

# the formats of the paths that end with each suffix
def Format.known() -> List<&2, Known>:
  +css = Format.imports("@import ", "\"", "\"", "")
  +js = Format.imports("import ", "from \"", "\"", "")
  +c: Format = Format.code{
    Format.leaf{Leaf.lines{}},
    Rule{
      Shared.Bytes.of_text("#include"),
      Shared.Bytes.of_text("\""),
      Shared.Bytes.of_text("\""),
      [],
      Shared.Bytes.of_text("#if"),
      Shared.Bytes.of_text("#else"),
      Shared.Bytes.of_text("#endif")
    }
  }
  +html: Format = Format.embed{
    Format.embed{
      Format.imports("<script src=\"", "", "\"", ""),
      Shared.Bytes.of_text("<style>"),
      Shared.Bytes.of_text("</style>"),
      css
    },
    Shared.Bytes.of_text("<script>"),
    Shared.Bytes.of_text("</script>"),
    js
  }
  [
    Known{".bend", Format.imports("import ", "", " ", "as ")},
    Known{".c", c},
    Known{".h", c},
    Known{".js", js},
    Known{".mjs", js},
    Known{".ts", js},
    Known{".css", css},
    Known{".html", html},
    Known{".htm", html},
    Known{".module", Format.leaf{Leaf.module{}}},
    Known{".png", Format.leaf{Leaf.whole{}}},
    Known{".jpg", Format.leaf{Leaf.whole{}}},
    Known{".gif", Format.leaf{Leaf.whole{}}},
    Known{".pdf", Format.leaf{Leaf.whole{}}},
    Known{".zip", Format.leaf{Leaf.whole{}}},
    Known{".wasm", Format.leaf{Leaf.whole{}}},
    Known{
      ".md",
      Format.embed{
        Format.leaf{Leaf.lines{}},
        Shared.Bytes.of_text("```"),
        Shared.Bytes.of_text("```"),
        Format.leaf{Leaf.lines{}}
      }
    }
  ]

# the format of the first suffix of ks that the path p ends with: lines when
# none does
def Format.find(ks: List<&2, Known>, +p: String) -> Format:
  match ks:
    case Nil{}:
      Format.leaf{Leaf.lines{}}
    case Con{Known{k, f}, r}:
      Shared.Bool.when(Format, String.ends_with(p, k), u => f, u => Format.find(r, p))

# the format of a resource at the path p, by its suffix
def Format.of(p: String) -> Format:
  Format.find(Format.known(), p)

# Merges apart
# ------------

# no two cuts each end before the other starts
def Plain.apart(
  cx: Cut,
  cy: Cut
) -> {Plain.before(cx, cy) == True{}: Bool} -> {Plain.before(cy, cx) == True{}: Bool} -> Empty:
  match cx cy:
    case Cut{sx, ox, nx, ex} Cut{sy, oy, ny, ey}:
      +kx = List.length(&2, Shared.Bytes(), sx)
      +dx = List.length(&2, Shared.Bytes(), ox)
      +ky = List.length(&2, Shared.Bytes(), sy)
      +dy = List.length(&2, Shared.Bytes(), oy)
      h1 => h2 =>
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_lt(kx, kx),
            True{},
            Equal.sym(Bool, Nat.is_lt(kx, kx), False{}, Shared.Nat.lt_irrefl(kx)),
            Shared.Nat.lt_le(
              kx,
              ky,
              kx
            )(
              Shared.Nat.le_lt(kx, Nat.add(kx, dx), ky)(Shared.Nat.le_add(kx, dx))(h1)
            )(
              Shared.Nat.lt_weak(
                ky,
                kx
              )(Shared.Nat.le_lt(ky, Nat.add(ky, dy), kx)(Shared.Nat.le_add(ky, dy))(h2))
            )
          )
        )

# the patch of a cut, applied to a, makes the cut's change to the lines of a
def Cut.apply_patch(
  c: Cut,
  a: Shared.Bytes()
) -> {Plain.apply(a, Lines.patch(c)) == Lines.bytes(Cut.apply(c, Lines.list(a))): Shared.Bytes()}:
  match c:
    case Cut{s, o, n, e}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Format.merge in lines, once both sides are known to change the text
def Merge.apart.both(
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes(),
  hd: {Merge.decide(b, x, y) == Decision.both{}: Decision},
  hb: {Plain.is_text(b) == True{}: Bool},
  hx: {Plain.is_text(x) == True{}: Bool},
  hy: {Plain.is_text(y) == True{}: Bool}
) -> {
  Format.merge(
    Format.leaf{Leaf.lines{}},
    b,
    x,
    y
  )
    == Plain.merge.cuts(
      Lines.cut(Lines.list(b), Lines.list(x)),
      Lines.cut(Lines.list(b), Lines.list(y))
    ): Merged
}:
  %Equal.sym(Decision, Merge.decide(b, x, y), Decision.both{}, hd):
    {
      Merged.head(
        Format.merges(
          Format.leaf{Leaf.lines{}},
          [Job{b, x, y, Format.decide.on(_, Format.leaf{Leaf.lines{}}, b, x, y)}]
        )
      )
        == Plain.merge.cuts(
          Lines.cut(Lines.list(b), Lines.list(x)),
          Lines.cut(Lines.list(b), Lines.list(y))
        ): Merged
    }
  %Equal.sym(Bool, Plain.is_text(b), True{}, hb):
    {
      Plain.merge.text(
        Bool.and(_, Bool.and(Plain.is_text(x), Plain.is_text(y))),
        b,
        x,
        y
      )
        == Plain.merge.cuts(
          Lines.cut(Lines.list(b), Lines.list(x)),
          Lines.cut(Lines.list(b), Lines.list(y))
        ): Merged
    }
  %Equal.sym(Bool, Plain.is_text(x), True{}, hx):
    {
      Plain.merge.text(
        Bool.and(_, Plain.is_text(y)),
        b,
        x,
        y
      )
        == Plain.merge.cuts(
          Lines.cut(Lines.list(b), Lines.list(x)),
          Lines.cut(Lines.list(b), Lines.list(y))
        ): Merged
    }
  %Equal.sym(Bool, Plain.is_text(y), True{}, hy):
    {
      Plain.merge.text(
        _,
        b,
        x,
        y
      )
        == Plain.merge.cuts(
          Lines.cut(Lines.list(b), Lines.list(x)),
          Lines.cut(Lines.list(b), Lines.list(y))
        ): Merged
    }
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the line patch from b to x, applied to y, once b and x are text
def Merge.apart.patch(
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes(),
  hb: {Plain.is_text(b) == True{}: Bool},
  hx: {Plain.is_text(x) == True{}: Bool}
) -> {
  Plain.apply(
    y,
    Plain.diff(b, x)
  )
    == Lines.bytes(
      Cut.apply(Lines.cut(Lines.list(b), Lines.list(x)), Lines.list(y))
    ): Shared.Bytes()
}:
  %Equal.sym(Bool, Plain.is_text(b), True{}, hb):
    {
      Plain.apply(
        y,
        Plain.diff.by(Bool.and(_, Plain.is_text(x)), b, x)
      )
        == Lines.bytes(
          Cut.apply(Lines.cut(Lines.list(b), Lines.list(x)), Lines.list(y))
        ): Shared.Bytes()
    }
  %Equal.sym(Bool, Plain.is_text(x), True{}, hx):
    {
      Plain.apply(
        y,
        Plain.diff.by(_, b, x)
      )
        == Lines.bytes(
          Cut.apply(Lines.cut(Lines.list(b), Lines.list(x)), Lines.list(y))
        ): Shared.Bytes()
    }
  Cut.apply_patch(Lines.cut(Lines.list(b), Lines.list(x)), y)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# two different changes of a text, where the lines that x changes end before
# the ones that y changes start, merge into y with x's change made to it
law Format.merge_apart:
  for +b: Shared.Bytes()
  for +x: Shared.Bytes()
  for +y: Shared.Bytes()
  {Merge.decide(b, x, y) == Decision.both{}: Decision}
    -> {Plain.is_text(b) == True{}: Bool}
    -> {Plain.is_text(x) == True{}: Bool}
    -> {Plain.is_text(y) == True{}: Bool}
    -> {
      Plain.before(
        Lines.cut(Lines.list(b), Lines.list(x)),
        Lines.cut(Lines.list(b), Lines.list(y))
      )
        == True{}: Bool
    }
    -> {
      Format.merge(
        Format.leaf{Leaf.lines{}},
        b,
        x,
        y
      )
        == Merged.clean{Plain.apply(y, Plain.diff(b, x))}: Merged
    }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Format.merge_apart(b, x, y):
  +lb = Lines.list(b)
  cx = Lines.cut(lb, Lines.list(x))
  cy = Lines.cut(lb, Lines.list(y))
  hd => +hb => +hx => hy => he =>
    %Equal.sym(
      Merged,
      Format.merge(Format.leaf{Leaf.lines{}}, b, x, y),
      Plain.merge.cuts(cx, cy),
      Merge.apart.both(b, x, y, hd, hb, hx, hy)
    ):
      {_ == Merged.clean{Plain.apply(y, Plain.diff(b, x))}: Merged}
    %Equal.sym(
      Shared.Bytes(),
      Plain.apply(y, Plain.diff(b, x)),
      Lines.bytes(Cut.apply(cx, Lines.list(y))),
      Merge.apart.patch(b, x, y, hb, hx)
    ):
      {Plain.merge.cuts(cx, cy) == Merged.clean{_}: Merged}
    %Equal.sym(
      Bool,
      Plain.before(cx, cy),
      True{},
      he
    ): {
      Plain.merge.order(
        _,
        Plain.before(cy, cx),
        cx,
        cy
      )
        == Merged.clean{Lines.bytes(Cut.apply(cx, Lines.list(y)))}: Merged
    }
    %Equal.sym(
      List<&2, Shared.Bytes()>,
      Cut.right(cy),
      Lines.list(y),
      Lines.cut_right(lb, Lines.list(y))
    ):
      {
        Merged.clean{
          Lines.bytes(Cut.apply(cx, _))
        }
          == Merged.clean{Lines.bytes(Cut.apply(cx, Lines.list(y)))}: Merged
      }
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the mirror of Format.merge_apart: when the lines that y changes end before
# the ones that x changes start, the merge is x with y's change made to it
law Format.merge_apart_mirror:
  for +b: Shared.Bytes()
  for +x: Shared.Bytes()
  for +y: Shared.Bytes()
  {Merge.decide(b, x, y) == Decision.both{}: Decision}
    -> {Plain.is_text(b) == True{}: Bool}
    -> {Plain.is_text(x) == True{}: Bool}
    -> {Plain.is_text(y) == True{}: Bool}
    -> {
      Plain.before(
        Lines.cut(Lines.list(b), Lines.list(y)),
        Lines.cut(Lines.list(b), Lines.list(x))
      )
        == True{}: Bool
    }
    -> {
      Format.merge(
        Format.leaf{Leaf.lines{}},
        b,
        x,
        y
      )
        == Merged.clean{Plain.apply(x, Plain.diff(b, y))}: Merged
    }

# Format.merge_apart_mirror, once x is known to end before y starts or not
# (held)
def Merge.apart.mirror(
  held: Bool,
  cx: Cut,
  cy: Cut,
  x: Shared.Bytes(),
  ex: {Plain.before(cx, cy) == held: Bool},
  he: {Plain.before(cy, cx) == True{}: Bool},
  hr: {Cut.right(cx) == Lines.list(x): List<&2, Shared.Bytes()>}
) -> {
  Plain.merge.order(
    held,
    True{},
    cx,
    cy
  )
    == Merged.clean{Lines.bytes(Cut.apply(cy, Lines.list(x)))}: Merged
}:
  match held:
    case True{}:
      Empty.absurd(
        {
          Plain.merge.order(
            True{},
            True{},
            cx,
            cy
          )
            == Merged.clean{Lines.bytes(Cut.apply(cy, Lines.list(x)))}: Merged
        },
        Plain.apart(cx, cy)(ex)(he)
      )
    case False{}:
      %Equal.sym(List<&2, Shared.Bytes()>, Cut.right(cx), Lines.list(x), hr):
        {
          Merged.clean{
            Lines.bytes(Cut.apply(cy, _))
          }
            == Merged.clean{Lines.bytes(Cut.apply(cy, Lines.list(x)))}: Merged
        }
      {==}

def Format.merge_apart_mirror(b, x, y):
  +lb = Lines.list(b)
  +cx = Lines.cut(lb, Lines.list(x))
  +cy = Lines.cut(lb, Lines.list(y))
  hd => +hb => hx => +hy => +he =>
    %Equal.sym(
      Merged,
      Format.merge(Format.leaf{Leaf.lines{}}, b, x, y),
      Plain.merge.cuts(cx, cy),
      Merge.apart.both(b, x, y, hd, hb, hx, hy)
    ):
      {_ == Merged.clean{Plain.apply(x, Plain.diff(b, y))}: Merged}
    %Equal.sym(
      Shared.Bytes(),
      Plain.apply(x, Plain.diff(b, y)),
      Lines.bytes(Cut.apply(cy, Lines.list(x))),
      Merge.apart.patch(b, y, x, hb, hy)
    ):
      {Plain.merge.cuts(cx, cy) == Merged.clean{_}: Merged}
    %Equal.sym(
      Bool,
      Plain.before(cy, cx),
      True{},
      he
    ): {
      Plain.merge.order(
        Plain.before(cx, cy),
        _,
        cx,
        cy
      )
        == Merged.clean{Lines.bytes(Cut.apply(cy, Lines.list(x)))}: Merged
    }
    Merge.apart.mirror(
      Plain.before(cx, cy),
      cx,
      cy,
      x,
      {==},
      he,
      Lines.cut_right(lb, Lines.list(x))
    )
