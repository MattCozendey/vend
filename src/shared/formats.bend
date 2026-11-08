import Base
import ./bools.bend as Bools
import ./bytes.bend as Octets
import ./lists.bend as Lists
import ./maybes.bend as Maybes
import ./shared.bend as Shared
import ./words.bend as Words

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
  s: Octets.Bytes() & List<&2, Octets.Bytes()>
) -> Octets.Bytes()
  & List<&2, Octets.Bytes()>:
  match nl s:
    case True{} Tuple{l, ls}:
      ([], l <> ls)
    case False{} Tuple{l, ls}:
      (c <> l, ls)

# the lines of b, split at each '\n', as the line it starts with and the rest
def Lines.split(b: Octets.Bytes()) -> Octets.Bytes() & List<&2, Octets.Bytes()>:
  match b:
    case Nil{}:
      ([], [])
    case Con{+c, r}:
      Lines.split.on(U32.is_eq(c, 10), c, Lines.split(r))

# the bytes of the line l and then the lines ls, with a '\n' between each
def Lines.join(ls: List<&2, Octets.Bytes()>, l: Octets.Bytes()) -> Octets.Bytes():
  match ls:
    case Nil{}:
      l
    case Con{n, r}:
      List.append(&2, U32, l, 10 <> Lines.join(r, n))

# the bytes of a split
def Lines.join.of(s: Octets.Bytes() & List<&2, Octets.Bytes()>) -> Octets.Bytes():
  match s:
    case Tuple{l, ls}:
      Lines.join(ls, l)

# a byte before the first line comes first
def Lines.join_cons(
  ls: List<&2, Octets.Bytes()>,
  c: U32,
  l: Octets.Bytes()
) -> {Lines.join(ls, c <> l) == c <> Lines.join(ls, l): Octets.Bytes()}:
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
  s: Octets.Bytes() & List<&2, Octets.Bytes()>,
  r: Octets.Bytes(),
  e: {U32.is_eq(c, 10) == nl: Bool},
  ih: {Lines.join.of(s) == r: Octets.Bytes()}
) -> {Lines.join.of(Lines.split.on(nl, c, s)) == c <> r: Octets.Bytes()}:
  match nl s:
    case True{} Tuple{l, ls}:
      %Equal.sym(
        U32,
        c,
        10,
        Words.U32.is_eq_sound(c, 10)(e)
      ): {10 <> Lines.join(ls, l) == _ <> r: Octets.Bytes()}
      %ih: {10 <> Lines.join(ls, l) == 10 <> _: Octets.Bytes()}
      {==}
    case False{} Tuple{l, ls}:
      %Equal.sym(
        Octets.Bytes(),
        Lines.join(ls, c <> l),
        c <> Lines.join(ls, l),
        Lines.join_cons(ls, c, l)
      ):
        {_ == c <> r: Octets.Bytes()}
      %ih: {c <> Lines.join(ls, l) == c <> _: Octets.Bytes()}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines of b join back into b
law Lines.read_back:
  for b: Octets.Bytes()
  {Lines.join.of(Lines.split(b)) == b: Octets.Bytes()}

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
    start: List<&2, Octets.Bytes()>,
    old: List<&2, Octets.Bytes()>,
    new: List<&2, Octets.Bytes()>,
    end: List<&2, Octets.Bytes()>
  }

# the old lines of c, between its start and end
def Cut.left(c: Cut) -> List<&2, Octets.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Octets.Bytes(), s, List.append(&2, Octets.Bytes(), o, e))

# the new lines of c, between its start and end
def Cut.right(c: Cut) -> List<&2, Octets.Bytes()>:
  match c:
    case Cut{s, o, n, e}:
      List.append(&2, Octets.Bytes(), s, List.append(&2, Octets.Bytes(), n, e))

# the cut with the start s and the ends e
def Lines.cut.ends(s: List<&2, Octets.Bytes()>, e: Lists.Ends<Octets.Bytes()>) -> Cut:
  match e:
    case Lists.Ends{ea, eb, se}:
      Cut{s, ea, eb, se}

# the cut of a fork, by the ends of what follows its shared start
def Lines.cut.of(f: Lists.Fork<Octets.Bytes()>) -> Cut:
  match f:
    case Lists.Fork{s, ra, rb}:
      Lines.cut.ends(s, Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb))

# the lines that a and b share at the start and at the end, and what differs
def Lines.cut(a: List<&2, Octets.Bytes()>, b: List<&2, Octets.Bytes()>) -> Cut:
  Lines.cut.of(Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b))

# the old lines of a cut by ends e are its start, then the first list of e
def Lines.cut.ends_left(
  s: List<&2, Octets.Bytes()>,
  e: Lists.Ends<Octets.Bytes()>
) -> {
  Cut.left(
    Lines.cut.ends(s, e)
  )
    == List.append(
      &2,
      Octets.Bytes(),
      s,
      Lists.Ends.left(Octets.Bytes(), e)
    ): List<&2, Octets.Bytes()>
}:
  match e:
    case Lists.Ends{ea, eb, se}:
      {==}

# the new lines of a cut by ends e are its start, then the second list of e
def Lines.cut.ends_right(
  s: List<&2, Octets.Bytes()>,
  e: Lists.Ends<Octets.Bytes()>
) -> {
  Cut.right(
    Lines.cut.ends(s, e)
  )
    == List.append(
      &2,
      Octets.Bytes(),
      s,
      Lists.Ends.right(Octets.Bytes(), e)
    ): List<&2, Octets.Bytes()>
}:
  match e:
    case Lists.Ends{ea, eb, se}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the old lines of the cut of a fork are its first list
def Lines.cut.of_left(
  f: Lists.Fork<Octets.Bytes()>
) -> {Cut.left(Lines.cut.of(f)) == Lists.Fork.left(Octets.Bytes(), f): List<&2, Octets.Bytes()>}:
  match f:
    case Lists.Fork{s, +ra, +rb}:
      e = Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb)
      Equal.trans(
        List<&2, Octets.Bytes()>,
        Cut.left(Lines.cut.ends(s, e)),
        List.append(&2, Octets.Bytes(), s, Lists.Ends.left(Octets.Bytes(), e)),
        List.append(&2, Octets.Bytes(), s, ra),
        Lines.cut.ends_left(s, e),
        Equal.cong(
          List<&2, Octets.Bytes()>,
          List<&2, Octets.Bytes()>,
          z => List.append(&2, Octets.Bytes(), s, z),
          Lists.Ends.left(Octets.Bytes(), e),
          ra,
          Lists.List.ends_left(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb)
        )
      )

# the new lines of the cut of a fork are its second list
def Lines.cut.of_right(
  f: Lists.Fork<Octets.Bytes()>
) -> {Cut.right(Lines.cut.of(f)) == Lists.Fork.right(Octets.Bytes(), f): List<&2, Octets.Bytes()>}:
  match f:
    case Lists.Fork{s, +ra, +rb}:
      e = Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb)
      Equal.trans(
        List<&2, Octets.Bytes()>,
        Cut.right(Lines.cut.ends(s, e)),
        List.append(&2, Octets.Bytes(), s, Lists.Ends.right(Octets.Bytes(), e)),
        List.append(&2, Octets.Bytes(), s, rb),
        Lines.cut.ends_right(s, e),
        Equal.cong(
          List<&2, Octets.Bytes()>,
          List<&2, Octets.Bytes()>,
          z => List.append(&2, Octets.Bytes(), s, z),
          Lists.Ends.right(Octets.Bytes(), e),
          rb,
          Lists.List.ends_right(
            ~Octets.Bytes(),
            ~Octets.Bytes.is_eq,
            ~Octets.Bytes.is_eq_sound,
            ra,
            rb
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the old lines
law Lines.cut_left:
  for +a: List<&2, Octets.Bytes()>
  for +b: List<&2, Octets.Bytes()>
  {Cut.left(Lines.cut(a, b)) == a: List<&2, Octets.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_left(a, b):
  f = Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Octets.Bytes()>,
    Cut.left(Lines.cut.of(f)),
    Lists.Fork.left(Octets.Bytes(), f),
    a,
    Lines.cut.of_left(f),
    Lists.List.fork_left(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a cut gives back the new lines
law Lines.cut_right:
  for +a: List<&2, Octets.Bytes()>
  for +b: List<&2, Octets.Bytes()>
  {Cut.right(Lines.cut(a, b)) == b: List<&2, Octets.Bytes()>}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Lines.cut_right(a, b):
  f = Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Octets.Bytes()>,
    Cut.right(Lines.cut.of(f)),
    Lists.Fork.right(Octets.Bytes(), f),
    b,
    Lines.cut.of_right(f),
    Lists.List.fork_right(~Octets.Bytes(), ~Octets.Bytes.is_eq, ~Octets.Bytes.is_eq_sound, a, b)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the lines a after a patch: keep the first keep lines, drop the next drop, and
# put the lines put in their place
def Lines.apply(
  keep: Nat,
  a: List<&2, Octets.Bytes()>,
  drop: Nat,
  put: List<&2, Octets.Bytes()>
) -> List<&2, Octets.Bytes()>:
  match keep a:
    case 0n x:
      List.append(&2, Octets.Bytes(), put, List.drop(&2, Octets.Bytes(), x, drop))
    case 1n+k Nil{}:
      put
    case 1n+k Con{l, r}:
      l <> Lines.apply(k, r, drop, put)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# applying the patch of a cut to its old lines gives its new lines
def Lines.apply_cut(
  s: List<&2, Octets.Bytes()>,
  o: List<&2, Octets.Bytes()>,
  n: List<&2, Octets.Bytes()>,
  e: List<&2, Octets.Bytes()>
) -> {
  Lines.apply(
    List.length(&2, Octets.Bytes(), s),
    Cut.left(Cut{s, o, n, e}),
    List.length(&2, Octets.Bytes(), o),
    n
  )
    == Cut.right(Cut{s, o, n, e}): List<&2, Octets.Bytes()>
}:
  match s:
    case Nil{}:
      %Equal.sym(
        List<&2, Octets.Bytes()>,
        List.drop(
          &2,
          Octets.Bytes(),
          List.append(&2, Octets.Bytes(), o, e),
          List.length(&2, Octets.Bytes(), o)
        ),
        e,
        Lists.List.drop_after_append(Octets.Bytes(), o, e)
      ):
        {
          List.append(
            &2,
            Octets.Bytes(),
            n,
            _
          )
            == List.append(&2, Octets.Bytes(), n, e): List<&2, Octets.Bytes()>
        }
      {==}
    case Con{l, r}:
      %Equal.sym(
        List<&2, Octets.Bytes()>,
        Lines.apply(
          List.length(&2, Octets.Bytes(), r),
          Cut.left(Cut{r, o, n, e}),
          List.length(&2, Octets.Bytes(), o),
          n
        ),
        Cut.right(Cut{r, o, n, e}),
        Lines.apply_cut(r, o, n, e)
      ):
        {l <> _ == l <> Cut.right(Cut{r, o, n, e}): List<&2, Octets.Bytes()>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# the lines of b
def Lines.list.of(s: Octets.Bytes() & List<&2, Octets.Bytes()>) -> List<&2, Octets.Bytes()>:
  match s:
    case Tuple{l, ls}:
      l <> ls

# the lines of b, as a list
def Lines.list(b: Octets.Bytes()) -> List<&2, Octets.Bytes()>:
  Lines.list.of(Lines.split(b))

# the bytes of the lines ls
def Lines.bytes(ls: List<&2, Octets.Bytes()>) -> Octets.Bytes():
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      Lines.join(r, l)

# the bytes of a split are the bytes of its lines
def Lines.bytes_of(
  s: Octets.Bytes() & List<&2, Octets.Bytes()>
) -> {Lines.bytes(Lines.list.of(s)) == Lines.join.of(s): Octets.Bytes()}:
  match s:
    case Tuple{l, ls}:
      {==}

# the lines of b give back b
law Lines.bytes_list:
  for b: Octets.Bytes()
  {Lines.bytes(Lines.list(b)) == b: Octets.Bytes()}

def Lines.bytes_list(b):
  +b = b
  Equal.trans(
    Octets.Bytes(),
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
  Patch.lines{keep: Nat, drop: Nat, put: List<&2, Octets.Bytes()>}
  Patch.whole{bytes: Octets.Bytes()}
  Patch.pieces{shape: List<&2, Shape>, texts: List<&2, Patch>, regions: List<&2, Patch>}

# x is not 0
def Plain.not_nul(x: U32) -> Bool:
  Bool.not(U32.is_eq(x, 0))

# b is text: no byte of it is 0
def Plain.is_text(b: Octets.Bytes()) -> Bool:
  List.all(~&2, ~U32, ~Plain.not_nul, b)

# the patch of the lines of a cut
def Lines.patch(c: Cut) -> Patch:
  match c:
    case Cut{s, o, n, e}:
      Patch.lines{List.length(&2, Octets.Bytes(), s), List.length(&2, Octets.Bytes(), o), n}

# the patch from a to b, as lines when both are text (text)
def Plain.diff.by(text: Bool, a: Octets.Bytes(), b: Octets.Bytes()) -> Patch:
  match text:
    case True{}:
      Lines.patch(Lines.cut(Lines.list(a), Lines.list(b)))
    case False{}:
      Patch.whole{b}

# the patch from a to b
def Plain.diff(+a: Octets.Bytes(), +b: Octets.Bytes()) -> Patch:
  Plain.diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# a after the patch p; a patch of an embedding leaves a as it is
def Plain.apply(a: Octets.Bytes(), p: Patch) -> Octets.Bytes():
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
  a: Octets.Bytes(),
  lb: List<&2, Octets.Bytes()>,
  hl: {Cut.left(c) == Lines.list(a): List<&2, Octets.Bytes()>},
  hr: {Cut.right(c) == lb: List<&2, Octets.Bytes()>}
) -> {Plain.apply(a, Lines.patch(c)) == Lines.bytes(lb): Octets.Bytes()}:
  match c:
    case Cut{s, o, n, e}:
      Equal.cong(
        List<&2, Octets.Bytes()>,
        Octets.Bytes(),
        z => Lines.bytes(z),
        Lines.apply(List.length(&2, Octets.Bytes(), s), Lines.list(a), List.length(&2, Octets.Bytes(), o), n),
        lb,
        %hl: {Lines.apply(List.length(&2, Octets.Bytes(), s), _, List.length(&2, Octets.Bytes(), o), n) == lb: List<&2, Octets.Bytes()>}
        %hr: {Lines.apply(List.length(&2, Octets.Bytes(), s), Cut.left(Cut{s, o, n, e}), List.length(&2, Octets.Bytes(), o), n) == _: List<&2, Octets.Bytes()>}
        Lines.apply_cut(s, o, n, e))

# Plain.apply_diff, by whether both are text (text)
def Plain.apply_diff.by(
  text: Bool,
  +a: Octets.Bytes(),
  +b: Octets.Bytes()
) -> {Plain.apply(a, Plain.diff.by(text, a, b)) == b: Octets.Bytes()}:
  match text:
    case True{}:
      +la = Lines.list(a)
      +lb = Lines.list(b)
      Equal.trans(
        Octets.Bytes(),
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
  for +a: Octets.Bytes()
  for +b: Octets.Bytes()
  {Plain.apply(a, Plain.diff(a, b)) == b: Octets.Bytes()}

def Plain.apply_diff(a, b):
  Plain.apply_diff.by(Bool.and(Plain.is_text(a), Plain.is_text(b)), a, b)

# Merges
# ------
# A merge of x and y, two changes of b. Before any format looks, Merge.decide
# takes the one change when only one side changed, or when both made the same
# change; so these merges hold for every format (Format.merge_*). A format
# merges only what both sides changed, differently. Plain text merges by
# lines: two hunks merge when one ends before the other starts.

# a merge: its bytes, or a clash
type Merged is Data:
  Merged.clean{bytes: Octets.Bytes()}
  Merged.clash{}

# the lines lb after two patches, x's first when it ends before y's starts
# (x_first), y's first when it ends before x's starts (y_first)
def Plain.merge.order(
  x_first: Bool,
  y_first: Bool,
  lb: List<&2, Octets.Bytes()>,
  kx: Nat,
  dx: Nat,
  nx: List<&2, Octets.Bytes()>,
  ky: Nat,
  dy: Nat,
  ny: List<&2, Octets.Bytes()>
) -> Merged:
  match x_first y_first:
    case True{} w:
      Merged.clean{Lines.bytes(Lines.apply(kx, Lines.apply(ky, lb, dy, ny), dx, nx))}
    case False{} True{}:
      Merged.clean{Lines.bytes(Lines.apply(ky, Lines.apply(kx, lb, dx, nx), dy, ny))}
    case False{} False{}:
      Merged.clash{}

# the merge of the cuts cx and cy of the lines lb
def Plain.merge.cuts(lb: List<&2, Octets.Bytes()>, cx: Cut, cy: Cut) -> Merged:
  match cx cy:
    case Cut{sx, ox, nx, ex} Cut{sy, oy, ny, ey}:
      +kx = List.length(&2, Octets.Bytes(), sx)
      +dx = List.length(&2, Octets.Bytes(), ox)
      +ky = List.length(&2, Octets.Bytes(), sy)
      +dy = List.length(&2, Octets.Bytes(), oy)
      Plain.merge.order(
        Nat.is_lt(Nat.add(kx, dx), ky),
        Nat.is_lt(Nat.add(ky, dy), kx),
        lb,
        kx,
        dx,
        nx,
        ky,
        dy,
        ny
      )

# the merge of two text changes, by their lines
def Plain.merge.lines(b: Octets.Bytes(), x: Octets.Bytes(), y: Octets.Bytes()) -> Merged:
  +lb = Lines.list(b)
  Plain.merge.cuts(lb, Lines.cut(lb, Lines.list(x)), Lines.cut(lb, Lines.list(y)))

# the merge of two different changes, as lines when all three are text (text)
def Plain.merge.text(
  text: Bool,
  b: Octets.Bytes(),
  x: Octets.Bytes(),
  y: Octets.Bytes()
) -> Merged:
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
def Merge.decide.right(held: Bool, x: Octets.Bytes(), y: Octets.Bytes()) -> Decision:
  match held:
    case True{}:
      Decision.ours{}
    case False{}:
      Merge.decide.same(Octets.Bytes.is_eq(x, y))

# theirs when x is b (held), else as y is b or not
def Merge.decide.left(held: Bool, b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Decision:
  match held:
    case True{}:
      Decision.theirs{}
    case False{}:
      Merge.decide.right(Octets.Bytes.is_eq(y, b), x, y)

# what a merge of x and y, two changes of b, takes before any format looks
def Merge.decide(+b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Decision:
  Merge.decide.left(Octets.Bytes.is_eq(x, b), b, x, y)

# the change that the decision d takes of x and y, none for both
def Decision.take(d: Decision, x: Octets.Bytes(), y: Octets.Bytes()) -> Maybe<&2, Octets.Bytes()>:
  match d:
    case Decision.theirs{}:
      Some{y}
    case Decision.ours{}:
      Some{x}
    case Decision.both{}:
      None{}
    case Decision.pieces{}:
      None{}

# Merge.left_only once x is known to be b or not (held)
def Merge.left_only.at(
  held: Bool,
  +b: Octets.Bytes(),
  +x: Octets.Bytes(),
  e: {Octets.Bytes.is_eq(x, b) == held: Bool}
) -> {Decision.take(Merge.decide.left(held, b, x, b), x, b) == Some{x}: Maybe<&2, Octets.Bytes()>}:
  match held:
    case True{}:
      %Equal.sym(Octets.Bytes(), x, b, Octets.Bytes.is_eq_sound(x, b)(e)): {Some{b} == Some{_}: Maybe<&2, Octets.Bytes()>}
      {==}
    case False{}:
      %Equal.sym(Bool, Octets.Bytes.is_eq(b, b), True{}, Octets.Bytes.is_eq_refl(b)):
        {Decision.take(Merge.decide.right(_, x, b), x, b) == Some{x}: Maybe<&2, Octets.Bytes()>}
      {==}

# when only x changed b, the decision takes x
def Merge.left_only(+b: Octets.Bytes(), +x: Octets.Bytes()) -> {Decision.take(Merge.decide(b, x, b), x, b) == Some{x}: Maybe<&2, Octets.Bytes()>}:
  Merge.left_only.at(Octets.Bytes.is_eq(x, b), b, x, {==})

# when only y changed b, the decision takes y
def Merge.right_only(+b: Octets.Bytes(), +y: Octets.Bytes()) -> {Decision.take(Merge.decide(b, b, y), b, y) == Some{y}: Maybe<&2, Octets.Bytes()>}:
  %Equal.sym(Bool, Octets.Bytes.is_eq(b, b), True{}, Octets.Bytes.is_eq_refl(b)):
    {Decision.take(Merge.decide.left(_, b, b, y), b, y) == Some{y}: Maybe<&2, Octets.Bytes()>}
  {==}

# Merge.same once x is known to be b or not (held)
def Merge.same.at(
  held: Bool,
  +b: Octets.Bytes(),
  +x: Octets.Bytes(),
  e: {Octets.Bytes.is_eq(x, b) == held: Bool}
) -> {Decision.take(Merge.decide.left(held, b, x, x), x, x) == Some{x}: Maybe<&2, Octets.Bytes()>}:
  match held:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Octets.Bytes.is_eq(x, b), False{}, e):
        {Decision.take(Merge.decide.right(_, x, x), x, x) == Some{x}: Maybe<&2, Octets.Bytes()>}
      %Equal.sym(Bool, Octets.Bytes.is_eq(x, x), True{}, Octets.Bytes.is_eq_refl(x)):
        {Decision.take(Merge.decide.same(_), x, x) == Some{x}: Maybe<&2, Octets.Bytes()>}
      {==}

# when both made the same change, the decision takes it
def Merge.same(+b: Octets.Bytes(), +x: Octets.Bytes()) -> {Decision.take(Merge.decide(b, x, x), x, x) == Some{x}: Maybe<&2, Octets.Bytes()>}:
  Merge.same.at(Octets.Bytes.is_eq(x, b), b, x, {==})

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
  Piece.text{bytes: Octets.Bytes()}
  Piece.region{bytes: Octets.Bytes(), closed: Bool}

# what kind a piece is, without its bytes
type Shape is Data:
  Shape.text{}
  Shape.region{closed: Bool}

# where p first occurs in some bytes: the bytes before it, and after it
type Found is Data:
  Found{before: Octets.Bytes(), after: Octets.Bytes()}

# b starts with p
def Bytes.starts(p: Octets.Bytes(), b: Octets.Bytes()) -> Bool:
  match p b:
    case Nil{} w:
      True{}
    case Con{x, pr} Con{y, br}:
      Bool.and(U32.is_eq(x, y), Bytes.starts(pr, br))
    case Con{x, pr} Nil{}:
      False{}

# the place found at x <> r, when p starts there (hit), else the place in r
def Bytes.find.at(hit: Bool, +p: Octets.Bytes(), +x: U32, +r: Octets.Bytes(), rest: Maybe<&2, Found>) -> Maybe<&2, Found>:
  match hit rest:
    case True{} m:
      Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}}
    case False{} None{}:
      None{}
    case False{} Some{Found{u, w}}:
      Some{Found{x <> u, w}}

# where p first occurs in b, if it does
def Bytes.find(+p: Octets.Bytes(), b: Octets.Bytes()) -> Maybe<&2, Found>:
  match b:
    case Nil{}:
      Bool.pick(Maybe<&2, Found>, List.is_empty(&2, U32, p), Some{Found{[], []}}, None{})
    case Con{+x, +r}:
      Bytes.find.at(Bytes.starts(p, x <> r), p, x, r, Bytes.find(p, r))

# the pieces of b, f steps at most: looking for an opening marker op (opening),
# or for the closing marker cl of a region (not opening); m is where the marker
# looked for first occurs in b
def Embed.split.go(
  f: Nat,
  +op: Octets.Bytes(),
  +cl: Octets.Bytes(),
  +b: Octets.Bytes(),
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
def Embed.split(+op: Octets.Bytes(), +cl: Octets.Bytes(), +b: Octets.Bytes()) -> List<&2, Piece>:
  Embed.split.go(1n+List.length(&2, U32, b), op, cl, b, True{}, Bytes.find(op, b))

# the bytes of the pieces ps, with the markers op and cl around each region
def Embed.join(+op: Octets.Bytes(), +cl: Octets.Bytes(), ps: List<&2, Piece>) -> Octets.Bytes():
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      List.append(&2, U32, t, Embed.join(op, cl, r))
    case Con{Piece.region{c, True{}}, r}:
      List.append(&2, U32, op, List.append(&2, U32, c, List.append(&2, U32, cl, Embed.join(op, cl, r))))
    case Con{Piece.region{c, False{}}, r}:
      List.append(&2, U32, op, List.append(&2, U32, c, Embed.join(op, cl, r)))

# the bytes before a found place
def Found.before(m: Maybe<&2, Found>) -> Octets.Bytes():
  match m:
    case Some{Found{u, w}}:
      u
    case None{}:
      []

# the bytes after a found place
def Found.after(m: Maybe<&2, Found>) -> Octets.Bytes():
  match m:
    case Some{Found{u, w}}:
      w
    case None{}:
      []

# bytes that start with p are p, then the rest
def Bytes.starts_drop(p: Octets.Bytes(), b: Octets.Bytes()) -> {Bytes.starts(p, b) == True{}: Bool} -> {
  b == List.append(&2, U32, p, List.drop(&2, U32, b, List.length(&2, U32, p))): Octets.Bytes()
}:
  match p b:
    case Nil{} w:
      h => Equal.sym(Octets.Bytes(), List.drop(&2, U32, w, 0n), w, Lists.List.drop_zero(&2, U32, w))
    case Con{+x, +pr} Con{+y, +br}:
      +h =>
        %Equal.sym(U32, x, y, Words.U32.is_eq_sound(x, y)(Bools.Bool.and_true_left(U32.is_eq(x, y), Bytes.starts(pr, br))(h))):
          {y <> br == _ <> List.append(&2, U32, pr, List.drop(&2, U32, br, List.length(&2, U32, pr))): Octets.Bytes()}
        %Bytes.starts_drop(pr, br)(Bools.Bool.and_true_right(U32.is_eq(x, y), Bytes.starts(pr, br))(h)):
          {y <> br == y <> _: Octets.Bytes()}
        {==}
    case Con{x, pr} Nil{}:
      h => Empty.absurd(
        {Nil{} == List.append(&2, U32, x <> pr, List.drop(&2, U32, Nil{}, List.length(&2, U32, x <> pr))): Octets.Bytes()},
        Shared.Bool.false_ne_true(h)
      )

# Bytes.find_cut at x <> r, by whether p starts there (hit)
def Bytes.find_cut.at(
  -u: Octets.Bytes(),
  -w: Octets.Bytes(),
  hit: Bool,
  +p: Octets.Bytes(),
  +x: U32,
  +r: Octets.Bytes(),
  rest: Maybe<&2, Found>,
  eh: {Bytes.starts(p, x <> r) == hit: Bool},
  ih: @u2: Octets.Bytes() -> @w2: Octets.Bytes() -> {rest == Some{Found{u2, w2}}: Maybe<&2, Found>} -> {
    r == List.append(&2, U32, u2, List.append(&2, U32, p, w2)): Octets.Bytes()
  }
) -> {Bytes.find.at(hit, p, x, r, rest) == Some{Found{u, w}}: Maybe<&2, Found>} -> {
  x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Octets.Bytes()
}:
  match hit rest:
    case True{} m:
      +h =>
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.before(z), Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}}, Some{Found{u, w}}, h):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Octets.Bytes()}
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.after(z), Some{Found{[], List.drop(&2, U32, x <> r, List.length(&2, U32, p))}}, Some{Found{u, w}}, h):
          {x <> r == List.append(&2, U32, p, _): Octets.Bytes()}
        Bytes.starts_drop(p, x <> r)(eh)
    case False{} None{}:
      h => Empty.absurd(
        {x <> r == List.append(&2, U32, u, List.append(&2, U32, p, w)): Octets.Bytes()},
        Maybes.Maybe.none_ne_some(Found, Found{u, w}, h)
      )
    case False{} Some{Found{+u2, +w2}}:
      +h =>
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.before(z), Some{Found{x <> u2, w2}}, Some{Found{u, w}}, h):
          {x <> r == List.append(&2, U32, _, List.append(&2, U32, p, w)): Octets.Bytes()}
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.after(z), Some{Found{x <> u2, w2}}, Some{Found{u, w}}, h):
          {x <> r == x <> List.append(&2, U32, u2, List.append(&2, U32, p, _)): Octets.Bytes()}
        %ih(u2)(w2)({==}): {x <> r == x <> _: Octets.Bytes()}
        {==}

# what Bytes.find finds cuts b: the bytes before, the pattern, the bytes after
def Bytes.find_cut(-u: Octets.Bytes(), -w: Octets.Bytes(), b: Octets.Bytes(), +p: Octets.Bytes()) -> {
  Bytes.find(p, b) == Some{Found{u, w}}: Maybe<&2, Found>
} -> {b == List.append(&2, U32, u, List.append(&2, U32, p, w)): Octets.Bytes()}:
  match b p:
    case Nil{} Nil{}:
      +h =>
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.before(z), Some{Found{[], []}}, Some{Found{u, w}}, h):
          {Nil{} == List.append(&2, U32, _, List.append(&2, U32, Nil{}, w)): Octets.Bytes()}
        %Equal.cong(Maybe<&2, Found>, Octets.Bytes(), z => Found.after(z), Some{Found{[], []}}, Some{Found{u, w}}, h):
          {Nil{} == List.append(&2, U32, Nil{}, List.append(&2, U32, Nil{}, _)): Octets.Bytes()}
        {==}
    case Nil{} Con{y, q}:
      h => Empty.absurd(
        {Nil{} == List.append(&2, U32, u, List.append(&2, U32, y <> q, w)): Octets.Bytes()},
        Maybes.Maybe.none_ne_some(Found, Found{u, w}, h)
      )
    case Con{+x, +r} m:
      Bytes.find_cut.at(u, w, Bytes.starts(m, x <> r), m, x, r, Bytes.find(m, r), {==}, u2 => w2 => e => Bytes.find_cut(u2, w2, r, m)(e))

# the marker that a split looks for: op outside a region (opening), cl inside
def Embed.marker(opening: Bool, op: Octets.Bytes(), cl: Octets.Bytes()) -> Octets.Bytes():
  match opening:
    case True{}:
      op
    case False{}:
      cl

# the bytes that the pieces of a split stand for: b outside a region
# (opening), else the opening marker op, then b
def Embed.whole(opening: Bool, op: Octets.Bytes(), b: Octets.Bytes()) -> Octets.Bytes():
  match opening:
    case True{}:
      b
    case False{}:
      List.append(&2, U32, op, b)

# the pieces of a split, joined, give back what they stand for
def Embed.join_split.go(
  f: Nat,
  +op: Octets.Bytes(),
  +cl: Octets.Bytes(),
  +b: Octets.Bytes(),
  opening: Bool,
  m: Maybe<&2, Found>,
  hm: @u: Octets.Bytes() -> @w: Octets.Bytes() -> {m == Some{Found{u, w}}: Maybe<&2, Found>} -> {
    b == List.append(&2, U32, u, List.append(&2, U32, Embed.marker(opening, op, cl), w)): Octets.Bytes()
  }
) -> {Embed.join(op, cl, Embed.split.go(f, op, cl, b, opening, m)) == Embed.whole(opening, op, b): Octets.Bytes()}:
  match f opening m:
    case 0n True{} n:
      Lists.List.append_nil(U32, b)
    case 0n False{} n:
      Equal.cong(Octets.Bytes(), Octets.Bytes(), z => List.append(&2, U32, op, z), List.append(&2, U32, b, []), b, Lists.List.append_nil(U32, b))
    case 1n+e True{} None{}:
      Lists.List.append_nil(U32, b)
    case 1n+e True{} Some{Found{+u, +w}}:
      %Equal.sym(
        Octets.Bytes(),
        Embed.join(op, cl, Embed.split.go(e, op, cl, w, False{}, Bytes.find(cl, w))),
        List.append(&2, U32, op, w),
        Embed.join_split.go(e, op, cl, w, False{}, Bytes.find(cl, w), u2 => w2 => h => Bytes.find_cut(u2, w2, w, cl)(h))
      ):
        {List.append(&2, U32, u, _) == b: Octets.Bytes()}
      Equal.sym(Octets.Bytes(), b, List.append(&2, U32, u, List.append(&2, U32, op, w)), hm(u)(w)({==}))
    case 1n+e False{} None{}:
      Equal.cong(Octets.Bytes(), Octets.Bytes(), z => List.append(&2, U32, op, z), List.append(&2, U32, b, []), b, Lists.List.append_nil(U32, b))
    case 1n+e False{} Some{Found{+u, +w}}:
      %Equal.sym(
        Octets.Bytes(),
        Embed.join(op, cl, Embed.split.go(e, op, cl, w, True{}, Bytes.find(op, w))),
        w,
        Embed.join_split.go(e, op, cl, w, True{}, Bytes.find(op, w), u2 => w2 => h => Bytes.find_cut(u2, w2, w, op)(h))
      ):
        {List.append(&2, U32, op, List.append(&2, U32, u, List.append(&2, U32, cl, _))) == List.append(&2, U32, op, b): Octets.Bytes()}
      Equal.cong(
        Octets.Bytes(),
        Octets.Bytes(),
        z => List.append(&2, U32, op, z),
        List.append(&2, U32, u, List.append(&2, U32, cl, w)),
        b,
        Equal.sym(Octets.Bytes(), b, List.append(&2, U32, u, List.append(&2, U32, cl, w)), hm(u)(w)({==}))
      )

# the pieces of b, joined, give back b: an embedding loses nothing
law Embed.join_split:
  for +op: Octets.Bytes()
  for +cl: Octets.Bytes()
  for +b: Octets.Bytes()
  {Embed.join(op, cl, Embed.split(op, cl, b)) == b: Octets.Bytes()}

def Embed.join_split(op, cl, b):
  Embed.join_split.go(1n+List.length(&2, U32, b), op, cl, b, True{}, Bytes.find(op, b), u => w => h => Bytes.find_cut(u, w, b, op)(h))

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
def Pieces.texts(ps: List<&2, Piece>) -> List<&2, Octets.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      t <> Pieces.texts(r)
    case Con{Piece.region{c, k}, r}:
      Pieces.texts(r)

# the bytes of the regions of ps, in order
def Pieces.regions(ps: List<&2, Piece>) -> List<&2, Octets.Bytes()>:
  match ps:
    case Nil{}:
      []
    case Con{Piece.text{t}, r}:
      Pieces.regions(r)
    case Con{Piece.region{c, k}, r}:
      c <> Pieces.regions(r)

# the pieces of the shapes sh, filled with the texts ts and the regions rs in
# order; a missing one is empty
def Pieces.build(sh: List<&2, Shape>, ts: List<&2, Octets.Bytes()>, rs: List<&2, Octets.Bytes()>) -> List<&2, Piece>:
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
def Pieces.build_of(ps: List<&2, Piece>) -> {Pieces.build(Pieces.shape(ps), Pieces.texts(ps), Pieces.regions(ps)) == ps: List<&2, Piece>}:
  match ps:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Piece.text{bytes}:
          %Equal.sym(List<&2, Piece>, Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)), tail, Pieces.build_of(tail)) :
            {Piece.text{bytes} <> _ == Piece.text{bytes} <> tail : List<&2, Piece>}
          {==}
        case Piece.region{bytes1, closed}:
          %Equal.sym(List<&2, Piece>, Pieces.build(Pieces.shape(tail), Pieces.texts(tail), Pieces.regions(tail)), tail, Pieces.build_of(tail)) :
            {Piece.region{bytes1, closed} <> _ == Piece.region{bytes1, closed} <> tail : List<&2, Piece>}
          {==}

# Changes
# -------
# What a patch does, part by part, for a reader.

# a part of a resource: its kind (line, content), where it is (a line counts
# from 1; a whole content is at 0), and its bytes
type Item is Data:
  Item{kind: String, place: Nat, bytes: Octets.Bytes()}

# a part that a patch added or removed
type Change is Data:
  Change.added{item: Item}
  Change.removed{item: Item}

# the lines ls as the changes that make (c), counted from the line at
def Lines.changes(
  ~make: Item -> Change,
  ls: List<&2, Octets.Bytes()>,
  +at: Nat
) -> List<&2, Change>:
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      make(Item{"line", at, l}) <> Lines.changes(~make, r, 1n+at)

# the changes of a whole content from a to b, none when they are the same
# (held)
def Plain.changes.whole(held: Bool, a: Octets.Bytes(), b: Octets.Bytes()) -> List<&2, Change>:
  match held:
    case True{}:
      []
    case False{}:
      [Change.removed{Item{"content", 0n, a}}, Change.added{Item{"content", 0n, b}}]

# the changes of the patch p of a
def Plain.changes.of(+a: Octets.Bytes(), p: Patch) -> List<&2, Change>:
  match p:
    case Patch.lines{+k, d, put}:
      List.append(
        &2,
        Change,
        Lines.changes(
          ~(i => Change.removed{i}),
          List.take(&2, Octets.Bytes(), List.drop(&2, Octets.Bytes(), Lines.list(a), k), d),
          1n+k
        ),
        Lines.changes(~(i => Change.added{i}), put, 1n+k)
      )
    case Patch.whole{+x}:
      Plain.changes.whole(Octets.Bytes.is_eq(a, x), a, x)
    case Patch.pieces{sh, ts, rs}:
      []

# what changed from a to b, part by part
def Plain.changes(+a: Octets.Bytes(), b: Octets.Bytes()) -> List<&2, Change>:
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
    start: Octets.Bytes(),
    open: Octets.Bytes(),
    close: Octets.Bytes(),
    alias: Octets.Bytes(),
    when: Octets.Bytes(),
    otherwise: Octets.Bytes(),
    end: Octets.Bytes()
  }

# a condition that an edge sits under: its line, and whether the edge is in
# its first part (holds) or after otherwise
type Cond is Data:
  Cond{test: Octets.Bytes(), holds: Bool}

# what a resource uses: the target as written, the name that it gets (empty
# without one), and the conditions that it sits under, innermost first
type Edge is Data:
  Edge{target: Octets.Bytes(), alias: Octets.Bytes(), conds: List<&2, Cond>}

# x is a space or a tab
def Line.is_blank(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9))

# l without its leading blanks
def Line.trim(l: Octets.Bytes()) -> Octets.Bytes():
  match l:
    case Nil{}:
      []
    case Con{+x, +r}:
      Bools.Bool.when(Octets.Bytes(), Line.is_blank(x), u => Line.trim(r), u => x <> r)

# l starts with the marker p, which is not empty
def Line.marks(+p: Octets.Bytes(), l: Octets.Bytes()) -> Bool:
  Bool.and(Bool.not(List.is_empty(&2, U32, p)), Bytes.starts(p, l))

# x cut where the marker m was found, when it is not empty (held): all of x
# comes before it when it is empty or not in x
def Rule.cut.of(held: Bool, m: Maybe<&2, Found>, x: Octets.Bytes()) -> Found:
  match held m:
    case True{} Some{f}:
      f
    case h n:
      Found{x, []}

# x cut at the first marker p
def Rule.cut(+p: Octets.Bytes(), +x: Octets.Bytes()) -> Found:
  Rule.cut.of(Bool.not(List.is_empty(&2, U32, p)), Bytes.find(p, x), x)

# the bytes after a cut
def Found.rest(c: Found) -> Octets.Bytes():
  match c:
    case Found{u, w}:
      w

# the edge whose target and what follows it are cut at the close marker (c),
# with the alias marker al, under the conditions cs
def Rule.named(c: Found, +al: Octets.Bytes(), cs: List<&2, Cond>) -> Edge:
  match c:
    case Found{t, +w}:
      Edge{t, Found.rest(Rule.cut(al, w)), cs}

# the edges of the bytes w after a start marker, once the open marker is
# known to be empty or not (held), and m is where it first occurs in w
def Rule.opened(
  held: Bool,
  m: Maybe<&2, Found>,
  +w: Octets.Bytes(),
  +cl: Octets.Bytes(),
  +al: Octets.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match held m:
    case False{} n:
      [Rule.named(Rule.cut(cl, w), al, cs)]
    case True{} None{}:
      []
    case True{} Some{Found{u, +a}}:
      [Rule.named(Rule.cut(cl, a), al, cs)]

# the edges of the trimmed line t, once it is known to start with the start
# marker st or not (started)
def Rule.line.at(
  started: Bool,
  +st: Octets.Bytes(),
  +t: Octets.Bytes(),
  +op: Octets.Bytes(),
  +cl: Octets.Bytes(),
  +al: Octets.Bytes(),
  cs: List<&2, Cond>
) -> List<&2, Edge>:
  match started:
    case True{}:
      +w = List.drop(&2, U32, t, List.length(&2, U32, st))
      Rule.opened(Bool.not(List.is_empty(&2, U32, op)), Bytes.find(op, w), w, cl, al, cs)
    case False{}:
      []

# the edges that the line l names under the conditions cs: one or none
def Rule.line(r: Rule, l: Octets.Bytes(), cs: List<&2, Cond>) -> List<&2, Edge>:
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
  t: Octets.Bytes(),
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
def Rule.step(r: Rule, l: Octets.Bytes(), cs: List<&2, Cond>) -> List<&2, Cond>:
  match r:
    case Rule{st, op, cl, al, wh, ot, en}:
      +t = Line.trim(l)
      Rule.step.at(Line.marks(en, t), Line.marks(ot, t), Line.marks(wh, t), t, cs)

# the edges of the lines ls under the conditions cs
def Rule.edges.go(ls: List<&2, Octets.Bytes()>, +r: Rule, +cs: List<&2, Cond>) -> List<&2, Edge>:
  match ls:
    case Nil{}:
      []
    case Con{+l, rest}:
      List.append(&2, Edge, Rule.line(r, l, cs), Rule.edges.go(rest, r, Rule.step(r, l, cs)))

# the edges of the bytes b
def Rule.edges(+r: Rule, b: Octets.Bytes()) -> List<&2, Edge>:
  Rule.edges.go(Lines.list(b), r, [])

# Nested formats
# --------------
# A format is lines (the default), whole, an embedding of an inner format in
# an outer one, or a language: a base format and the rule of its imports.
# Formats nest to any depth (CSS and JS inside HTML), and the laws below hold
# for every one. Each operation takes a list of items, so that an embedding
# hands all its texts to the outer format and all its regions to the inner one
# in one call; an old item that is missing is empty.
type Format is Data:
  Format.lines{}
  Format.whole{}
  Format.embed{outer: Format, open: Octets.Bytes(), close: Octets.Bytes(), inner: Format}
  Format.code{base: Format, rule: Rule}

# the first of the items xs, empty when there is none
def Items.first(xs: List<&2, Octets.Bytes()>) -> Octets.Bytes():
  Maybe.default(&2, Octets.Bytes(), List.head(&2, Octets.Bytes(), xs), [])

# the patches from the items as to the items bs, one for each of bs
def Format.diffs(f: Format, bs: List<&2, Octets.Bytes()>, +as: List<&2, Octets.Bytes()>) -> List<&2, Patch>:
  match f bs:
    case Format.lines{} Nil{}:
      []
    case Format.lines{} Con{+b, br}:
      Plain.diff(Items.first(as), b) <> Format.diffs(Format.lines{}, br, List.tail(&2, Octets.Bytes(), as))
    case Format.whole{} Nil{}:
      []
    case Format.whole{} Con{b, br}:
      Patch.whole{b} <> Format.diffs(Format.whole{}, br, List.tail(&2, Octets.Bytes(), as))
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{+b, br}:
      +pa = Embed.split(op, cl, Items.first(as))
      +pb = Embed.split(op, cl, b)
      Patch.pieces{
        Pieces.shape(pb),
        Format.diffs(o, Pieces.texts(pb), Pieces.texts(pa)),
        Format.diffs(i, Pieces.regions(pb), Pieces.regions(pa))
      }
        <> Format.diffs(Format.embed{o, op, cl, i}, br, List.tail(&2, Octets.Bytes(), as))
    case Format.code{base, r} c:
      Format.diffs(base, c, as)

# the items as after the patches ps, one for each of ps; a patch of another
# format applies as plain
def Format.applies(f: Format, ps: List<&2, Patch>, +as: List<&2, Octets.Bytes()>) -> List<&2, Octets.Bytes()>:
  match f ps:
    case Format.lines{} Nil{}:
      []
    case Format.lines{} Con{p, pr}:
      Plain.apply(Items.first(as), p) <> Format.applies(Format.lines{}, pr, List.tail(&2, Octets.Bytes(), as))
    case Format.whole{} Nil{}:
      []
    case Format.whole{} Con{p, pr}:
      Plain.apply(Items.first(as), p) <> Format.applies(Format.whole{}, pr, List.tail(&2, Octets.Bytes(), as))
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{Patch.pieces{sh, tps, rps}, pr}:
      +pa = Embed.split(op, cl, Items.first(as))
      Embed.join(
        op,
        cl,
        Pieces.build(sh, Format.applies(o, tps, Pieces.texts(pa)), Format.applies(i, rps, Pieces.regions(pa)))
      )
        <> Format.applies(Format.embed{o, op, cl, i}, pr, List.tail(&2, Octets.Bytes(), as))
    case Format.embed{+o, +op, +cl, +i} Con{p, pr}:
      Plain.apply(Items.first(as), p) <> Format.applies(Format.embed{o, op, cl, i}, pr, List.tail(&2, Octets.Bytes(), as))
    case Format.code{base, r} q:
      Format.applies(base, q, as)

# the patches from as to bs, applied to as, give bs, in every format
law Format.apply_diffs:
  for f: Format
  for +bs: List<&2, Octets.Bytes()>
  for +as: List<&2, Octets.Bytes()>
  {Format.applies(f, Format.diffs(f, bs, as), as) == bs: List<&2, Octets.Bytes()>}

def Format.apply_diffs(f, bs, as):
  match f bs:
    case Format.lines{} Nil{}:
      {==}
    case Format.lines{} Con{+b, br}:
      Lists.List.cons_eq(
        Octets.Bytes(),
        Plain.apply(Items.first(as), Plain.diff(Items.first(as), b)),
        b,
        Format.applies(Format.lines{}, Format.diffs(Format.lines{}, br, List.tail(&2, Octets.Bytes(), as)), List.tail(&2, Octets.Bytes(), as)),
        br,
        Plain.apply_diff(Items.first(as), b),
        Format.apply_diffs(Format.lines{}, br, List.tail(&2, Octets.Bytes(), as))
      )
    case Format.whole{} Nil{}:
      {==}
    case Format.whole{} Con{b, br}:
      %Equal.sym(
        List<&2, Octets.Bytes()>,
        Format.applies(Format.whole{}, Format.diffs(Format.whole{}, br, List.tail(&2, Octets.Bytes(), as)), List.tail(&2, Octets.Bytes(), as)),
        br,
        Format.apply_diffs(Format.whole{}, br, List.tail(&2, Octets.Bytes(), as))
      ): {b <> _ == b <> br: List<&2, Octets.Bytes()>}
      {==}
    case Format.embed{o, op, cl, i} Nil{}:
      {==}
    case Format.embed{+o, +op, +cl, +i} Con{+b, br}:
      +pa = Embed.split(op, cl, Items.first(as))
      +pb = Embed.split(op, cl, b)
      +ta = Pieces.texts(pa)
      +ra = Pieces.regions(pa)
      +tb = Pieces.texts(pb)
      +rb = Pieces.regions(pb)
      +rest = List.tail(&2, Octets.Bytes(), as)
      Lists.List.cons_eq(
        Octets.Bytes(),
        Embed.join(
          op,
          cl,
          Pieces.build(Pieces.shape(pb), Format.applies(o, Format.diffs(o, tb, ta), ta), Format.applies(i, Format.diffs(i, rb, ra), ra))
        ),
        b,
        Format.applies(Format.embed{o, op, cl, i}, Format.diffs(Format.embed{o, op, cl, i}, br, rest), rest),
        br,
        %Equal.sym(List<&2, Octets.Bytes()>, Format.applies(o, Format.diffs(o, tb, ta), ta), tb, Format.apply_diffs(o, tb, ta)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), _, Format.applies(i, Format.diffs(i, rb, ra), ra))) == b: Octets.Bytes()}
        %Equal.sym(List<&2, Octets.Bytes()>, Format.applies(i, Format.diffs(i, rb, ra), ra), rb, Format.apply_diffs(i, rb, ra)):
          {Embed.join(op, cl, Pieces.build(Pieces.shape(pb), tb, _)) == b: Octets.Bytes()}
        %Equal.sym(List<&2, Piece>, Pieces.build(Pieces.shape(pb), tb, rb), pb, Pieces.build_of(pb)):
          {Embed.join(op, cl, _) == b: Octets.Bytes()}
        Embed.join_split(op, cl, b),
        Format.apply_diffs(Format.embed{o, op, cl, i}, br, rest)
      )
    case Format.code{base, r} c:
      Format.apply_diffs(base, c, as)

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
def Embed.shape(+op: Octets.Bytes(), +cl: Octets.Bytes(), +b: Octets.Bytes()) -> List<&2, Shape>:
  Pieces.shape(Embed.split(op, cl, b))

# what to take when both changes differ, in the format f
def Format.decide.both(f: Format, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Decision:
  match f:
    case Format.lines{}:
      Decision.both{}
    case Format.whole{}:
      Decision.both{}
    case Format.embed{o, +op, +cl, i}:
      +sb = Embed.shape(op, cl, b)
      Bool.pick(
        Decision,
        Bool.and(
          Lists.List.same(~Shape, ~Shape.same, sb, Embed.shape(op, cl, x)),
          Lists.List.same(~Shape, ~Shape.same, sb, Embed.shape(op, cl, y))
        ),
        Decision.pieces{},
        Decision.both{}
      )
    case Format.code{base, r}:
      Format.decide.both(base, b, x, y)

# the decision d, in the format f
def Format.decide.on(d: Decision, f: Format, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Decision:
  match d:
    case Decision.both{}:
      Format.decide.both(f, b, x, y)
    case e:
      e

# what a merge of x and y, two changes of b, takes in the format f
def Format.decide(f: Format, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Decision:
  Format.decide.on(Merge.decide(b, x, y), f, b, x, y)

# a merge to make: the base, the two changes, and what to take
type Job is Data:
  Job{base: Octets.Bytes(), ours: Octets.Bytes(), theirs: Octets.Bytes(), decision: Decision}

# the job of merging x and y, two changes of b, in the format f
def Job.of(f: Format, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Job:
  Job{b, x, y, Format.decide(f, b, x, y)}

# the jobs of the items bs, xs and ys, place by place, in the format f
def Jobs.of(bs: List<&2, Octets.Bytes()>, +f: Format, +xs: List<&2, Octets.Bytes()>, +ys: List<&2, Octets.Bytes()>) -> List<&2, Job>:
  match bs:
    case Nil{}:
      []
    case Con{b, br}:
      Job.of(f, b, Items.first(xs), Items.first(ys))
        <> Jobs.of(br, f, List.tail(&2, Octets.Bytes(), xs), List.tail(&2, Octets.Bytes(), ys))

# the change that the decision d takes of x and y, a clash for both
def Merge.taken(d: Decision, x: Octets.Bytes(), y: Octets.Bytes()) -> Merged:
  match d:
    case Decision.theirs{}:
      Merged.clean{y}
    case Decision.ours{}:
      Merged.clean{x}
    case e:
      Merged.clash{}

# the merge of x and y, two changes of b, by lines, with the decision d
def Merge.plain(d: Decision, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  match d:
    case Decision.theirs{}:
      Merged.clean{y}
    case Decision.ours{}:
      Merged.clean{x}
    case e:
      Plain.merge.text(Bool.and(Plain.is_text(b), Bool.and(Plain.is_text(x), Plain.is_text(y))), b, x, y)

# the bytes x put before the bytes of a clean list m
def Merged.put(x: Octets.Bytes(), m: Maybe<&2, List<&2, Octets.Bytes()>>) -> Maybe<&2, List<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{x <> xs}

# the bytes of the merges ms, when none clashes
def Merged.all(ms: List<&2, Merged>) -> Maybe<&2, List<&2, Octets.Bytes()>>:
  match ms:
    case Nil{}:
      Some{[]}
    case Con{Merged.clean{x}, r}:
      Merged.put(x, Merged.all(r))
    case Con{Merged.clash{}, r}:
      None{}

# the embedding of the shape sh, with the merged texts mt and regions mr
def Merge.pieces(
  +op: Octets.Bytes(),
  +cl: Octets.Bytes(),
  sh: List<&2, Shape>,
  mt: Maybe<&2, List<&2, Octets.Bytes()>>,
  mr: Maybe<&2, List<&2, Octets.Bytes()>>
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

# the merges of the jobs js, in the format f. An embedding of one shape merges
# its texts in the outer format and its regions in the inner one; of other
# shapes, it merges as the outer format.
def Format.merges(f: Format, js: List<&2, Job>) -> List<&2, Merged>:
  match f js:
    case Format.lines{} Nil{}:
      []
    case Format.lines{} Con{Job{b, x, y, d}, jr}:
      Merge.plain(d, b, x, y) <> Format.merges(Format.lines{}, jr)
    case Format.whole{} Nil{}:
      []
    case Format.whole{} Con{Job{b, x, y, d}, jr}:
      Merge.taken(d, x, y) <> Format.merges(Format.whole{}, jr)
    case Format.embed{o, op, cl, i} Nil{}:
      []
    case Format.embed{+o, +op, +cl, +i} Con{Job{b, x, y, Decision.pieces{}}, jr}:
      +pb = Embed.split(op, cl, b)
      +px = Embed.split(op, cl, x)
      +py = Embed.split(op, cl, y)
      Merge.pieces(
        op,
        cl,
        Pieces.shape(pb),
        Merged.all(Format.merges(o, Jobs.of(Pieces.texts(pb), o, Pieces.texts(px), Pieces.texts(py)))),
        Merged.all(Format.merges(i, Jobs.of(Pieces.regions(pb), i, Pieces.regions(px), Pieces.regions(py))))
      )
        <> Format.merges(Format.embed{o, op, cl, i}, jr)
    case Format.embed{+o, +op, +cl, +i} Con{Job{+b, +x, +y, Decision.both{}}, jr}:
      Merged.head(Format.merges(o, [Job.of(o, b, x, y)])) <> Format.merges(Format.embed{o, op, cl, i}, jr)
    case Format.embed{+o, +op, +cl, +i} Con{Job{b, x, y, d}, jr}:
      Merge.taken(d, x, y) <> Format.merges(Format.embed{o, op, cl, i}, jr)
    case Format.code{base, r} q:
      Format.merges(base, q)

# the merge of x and y, two changes of b, in the format f
def Format.merge(+f: Format, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  Merged.head(Format.merges(f, [Job.of(f, b, x, y)]))

# a job whose decision takes z of its changes merges to z, in every format
def Format.merges_taken(
  f: Format,
  -b: Octets.Bytes(),
  -x: Octets.Bytes(),
  -y: Octets.Bytes(),
  -z: Octets.Bytes(),
  d: Decision,
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Octets.Bytes()>}
) -> {Format.merges(f, [Job{b, x, y, d}]) == [Merged.clean{z}]: List<&2, Merged>}:
  match f d:
    case Format.lines{} Decision.theirs{}:
      %Equal.sym(Octets.Bytes(), y, z, Maybes.Maybe.some_inj(Octets.Bytes(), y, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.lines{} Decision.ours{}:
      %Equal.sym(Octets.Bytes(), x, z, Maybes.Maybe.some_inj(Octets.Bytes(), x, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.lines{} Decision.both{}:
      Empty.absurd(
        {Format.merges(Format.lines{}, [Job{b, x, y, Decision.both{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.lines{} Decision.pieces{}:
      Empty.absurd(
        {Format.merges(Format.lines{}, [Job{b, x, y, Decision.pieces{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.whole{} Decision.theirs{}:
      %Equal.sym(Octets.Bytes(), y, z, Maybes.Maybe.some_inj(Octets.Bytes(), y, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.whole{} Decision.ours{}:
      %Equal.sym(Octets.Bytes(), x, z, Maybes.Maybe.some_inj(Octets.Bytes(), x, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.whole{} Decision.both{}:
      Empty.absurd(
        {Format.merges(Format.whole{}, [Job{b, x, y, Decision.both{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.whole{} Decision.pieces{}:
      Empty.absurd(
        {Format.merges(Format.whole{}, [Job{b, x, y, Decision.pieces{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.embed{o, op, cl, i} Decision.theirs{}:
      %Equal.sym(Octets.Bytes(), y, z, Maybes.Maybe.some_inj(Octets.Bytes(), y, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.embed{o, op, cl, i} Decision.ours{}:
      %Equal.sym(Octets.Bytes(), x, z, Maybes.Maybe.some_inj(Octets.Bytes(), x, z, h)): {[Merged.clean{_}] == [Merged.clean{z}]: List<&2, Merged>}
      {==}
    case Format.embed{o, op, cl, i} Decision.both{}:
      Empty.absurd(
        {Format.merges(Format.embed{o, op, cl, i}, [Job{b, x, y, Decision.both{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.embed{o, op, cl, i} Decision.pieces{}:
      Empty.absurd(
        {Format.merges(Format.embed{o, op, cl, i}, [Job{b, x, y, Decision.pieces{}}]) == [Merged.clean{z}]: List<&2, Merged>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Format.code{base, r} e:
      Format.merges_taken(base, b, x, y, z, e, h)

# a decision that takes z of the changes takes it in every format
def Format.decide.on_taken(
  d: Decision,
  -f: Format,
  -b: Octets.Bytes(),
  -x: Octets.Bytes(),
  -y: Octets.Bytes(),
  -z: Octets.Bytes(),
  h: {Decision.take(d, x, y) == Some{z}: Maybe<&2, Octets.Bytes()>}
) -> {Decision.take(Format.decide.on(d, f, b, x, y), x, y) == Some{z}: Maybe<&2, Octets.Bytes()>}:
  match d:
    case Decision.theirs{}:
      h
    case Decision.ours{}:
      h
    case Decision.both{}:
      Empty.absurd(
        {Decision.take(Format.decide.on(Decision.both{}, f, b, x, y), x, y) == Some{z}: Maybe<&2, Octets.Bytes()>},
        Maybes.Maybe.none_ne_some(Octets.Bytes(), z, h)
      )
    case Decision.pieces{}:
      h

# the merge of a job whose base decision takes z is z, in every format
def Format.merge_taken(
  +f: Format,
  +b: Octets.Bytes(),
  +x: Octets.Bytes(),
  +y: Octets.Bytes(),
  -z: Octets.Bytes(),
  h: {Decision.take(Merge.decide(b, x, y), x, y) == Some{z}: Maybe<&2, Octets.Bytes()>}
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
  for +b: Octets.Bytes()
  for +x: Octets.Bytes()
  {Format.merge(f, b, x, b) == Merged.clean{x}: Merged}

def Format.merge_left_only(f, b, x):
  Format.merge_taken(f, b, x, b, x, Merge.left_only(b, x))

# when only y changed b, a merge takes y, in every format
law Format.merge_right_only:
  for +f: Format
  for +b: Octets.Bytes()
  for +y: Octets.Bytes()
  {Format.merge(f, b, b, y) == Merged.clean{y}: Merged}

def Format.merge_right_only(f, b, y):
  Format.merge_taken(f, b, b, y, y, Merge.right_only(b, y))

# when both made the same change, a merge takes it, in every format
law Format.merge_same:
  for +f: Format
  for +b: Octets.Bytes()
  for +x: Octets.Bytes()
  {Format.merge(f, b, x, x) == Merged.clean{x}: Merged}

def Format.merge_same(f, b, x):
  Format.merge_taken(f, b, x, x, x, Merge.same(b, x))

# What a format reads
# -------------------

# what changed from a to b, part by part, as the format f shows it to a
# reader: an embedding shows the changes of its outer format, over all of it
def Format.changes(f: Format, +a: Octets.Bytes(), +b: Octets.Bytes()) -> List<&2, Change>:
  match f:
    case Format.lines{}:
      Plain.changes(a, b)
    case Format.whole{}:
      Plain.changes.whole(Octets.Bytes.is_eq(a, b), a, b)
    case Format.embed{o, op, cl, i}:
      Format.changes(o, a, b)
    case Format.code{base, r}:
      Format.changes(base, a, b)

# the edges of each of the items bs, by the rule r
def Rule.edges.of(bs: List<&2, Octets.Bytes()>, +r: Rule) -> List<&2, Edge>:
  match bs:
    case Nil{}:
      []
    case Con{b, br}:
      List.append(&2, Edge, Rule.edges(r, b), Rule.edges.of(br, r))

# the texts (texts) or the regions of each of the items bs, between the
# markers op and cl
def Embed.parts(bs: List<&2, Octets.Bytes()>, texts: Bool, +op: Octets.Bytes(), +cl: Octets.Bytes()) -> List<&2, Octets.Bytes()>:
  match bs texts:
    case Nil{} t:
      []
    case Con{b, br} True{}:
      List.append(&2, Octets.Bytes(), Pieces.texts(Embed.split(op, cl, b)), Embed.parts(br, True{}, op, cl))
    case Con{b, br} False{}:
      List.append(&2, Octets.Bytes(), Pieces.regions(Embed.split(op, cl, b)), Embed.parts(br, False{}, op, cl))

# what the items bs use, in the format f: the edges of each language, in the
# parts that it reads
def Format.uses(f: Format, +bs: List<&2, Octets.Bytes()>) -> List<&2, Edge>:
  match f:
    case Format.lines{}:
      []
    case Format.whole{}:
      []
    case Format.embed{o, +op, +cl, i}:
      List.append(&2, Edge, Format.uses(o, Embed.parts(bs, True{}, op, cl)), Format.uses(i, Embed.parts(bs, False{}, op, cl)))
    case Format.code{base, r}:
      List.append(&2, Edge, Rule.edges.of(bs, r), Format.uses(base, bs))

# Known formats
# -------------

# a language whose imports name a target after start, up to close
def Format.imports(start: String, open: String, close: String, alias: String) -> Format:
  Format.code{
    Format.lines{},
    Rule{
      Octets.Bytes.of_text(start),
      Octets.Bytes.of_text(open),
      Octets.Bytes.of_text(close),
      Octets.Bytes.of_text(alias),
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
    Format.lines{},
    Rule{
      Octets.Bytes.of_text("#include"),
      Octets.Bytes.of_text("\""),
      Octets.Bytes.of_text("\""),
      [],
      Octets.Bytes.of_text("#if"),
      Octets.Bytes.of_text("#else"),
      Octets.Bytes.of_text("#endif")
    }
  }
  +html: Format = Format.embed{
    Format.embed{
      Format.imports("<script src=\"", "", "\"", ""),
      Octets.Bytes.of_text("<style>"),
      Octets.Bytes.of_text("</style>"),
      css
    },
    Octets.Bytes.of_text("<script>"),
    Octets.Bytes.of_text("</script>"),
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
    Known{".md", Format.embed{Format.lines{}, Octets.Bytes.of_text("```"), Octets.Bytes.of_text("```"), Format.lines{}}}
  ]

# the format of the first suffix of ks that the path p ends with: lines when
# none does
def Format.find(ks: List<&2, Known>, +p: String) -> Format:
  match ks:
    case Nil{}:
      Format.lines{}
    case Con{Known{k, f}, r}:
      Bools.Bool.when(Format, String.ends_with(p, k), u => f, u => Format.find(r, p))

# the format of a resource at the path p, by its suffix
def Format.of(p: String) -> Format:
  Format.find(Format.known(), p)
