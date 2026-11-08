import Base
import ./bytes.bend as Octets
import ./lists.bend as Lists
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
) -> Octets.Bytes() & List<&2, Octets.Bytes()>:
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
def Lines.join_cons(ls: List<&2, Octets.Bytes()>, c: U32, l: Octets.Bytes()) -> {Lines.join(ls, c <> l) == c <> Lines.join(ls, l): Octets.Bytes()}:
  match ls:
    case Nil{}:
      {==}
    case Con{n, r}:
      {==}

# Lines.read_back once c is known to be '\n' or not (nl)
def Lines.read_back.on(
  nl: Bool,
  +c: U32,
  s: Octets.Bytes() & List<&2, Octets.Bytes()>,
  r: Octets.Bytes(),
  e: {U32.is_eq(c, 10) == nl: Bool},
  ih: {Lines.join.of(s) == r: Octets.Bytes()}
) -> {Lines.join.of(Lines.split.on(nl, c, s)) == c <> r: Octets.Bytes()}:
  match nl s:
    case True{} Tuple{l, ls}:
      %Equal.sym(U32, c, 10, Words.U32.is_eq_sound(c, 10)(e)) : {10 <> Lines.join(ls, l) == _ <> r: Octets.Bytes()}
      %ih : {10 <> Lines.join(ls, l) == 10 <> _: Octets.Bytes()}
      {==}
    case False{} Tuple{+l, +ls}:
      %Equal.sym(Octets.Bytes(), Lines.join(ls, c <> l), c <> Lines.join(ls, l), Lines.join_cons(ls, c, l)) :
        {_ == c <> r: Octets.Bytes()}
      %ih : {c <> Lines.join(ls, l) == c <> _: Octets.Bytes()}
      {==}

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
    case Lists.Fork{s, +ra, +rb}:
      Lines.cut.ends(s, Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb))

# the lines that a and b share at the start and at the end, and what differs
def Lines.cut(a: List<&2, Octets.Bytes()>, b: List<&2, Octets.Bytes()>) -> Cut:
  Lines.cut.of(Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b))

# the old lines of a cut by ends e are its start, then the first list of e
def Lines.cut.ends_left(s: List<&2, Octets.Bytes()>, e: Lists.Ends<Octets.Bytes()>) -> {Cut.left(Lines.cut.ends(s, e)) == List.append(&2, Octets.Bytes(), s, Lists.Ends.left(Octets.Bytes(), e)): List<&2, Octets.Bytes()>}:
  match e:
    case Lists.Ends{ea, eb, se}:
      {==}

# the new lines of a cut by ends e are its start, then the second list of e
def Lines.cut.ends_right(s: List<&2, Octets.Bytes()>, e: Lists.Ends<Octets.Bytes()>) -> {Cut.right(Lines.cut.ends(s, e)) == List.append(&2, Octets.Bytes(), s, Lists.Ends.right(Octets.Bytes(), e)): List<&2, Octets.Bytes()>}:
  match e:
    case Lists.Ends{ea, eb, se}:
      {==}

# the old lines of the cut of a fork are its first list
def Lines.cut.of_left(f: Lists.Fork<Octets.Bytes()>) -> {Cut.left(Lines.cut.of(f)) == Lists.Fork.left(Octets.Bytes(), f): List<&2, Octets.Bytes()>}:
  match f:
    case Lists.Fork{+s, +ra, +rb}:
      +e = Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb)
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
def Lines.cut.of_right(f: Lists.Fork<Octets.Bytes()>) -> {Cut.right(Lines.cut.of(f)) == Lists.Fork.right(Octets.Bytes(), f): List<&2, Octets.Bytes()>}:
  match f:
    case Lists.Fork{+s, +ra, +rb}:
      +e = Lists.List.ends(~Octets.Bytes(), ~Octets.Bytes.is_eq, ra, rb)
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
          Lists.List.ends_right(~Octets.Bytes(), ~Octets.Bytes.is_eq, ~Octets.Bytes.is_eq_sound, ra, rb)
        )
      )

# a cut gives back the old lines
law Lines.cut_left:
  for +a: List<&2, Octets.Bytes()>
  for +b: List<&2, Octets.Bytes()>
  {Cut.left(Lines.cut(a, b)) == a: List<&2, Octets.Bytes()>}

def Lines.cut_left(a, b):
  +f = Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Octets.Bytes()>,
    Cut.left(Lines.cut.of(f)),
    Lists.Fork.left(Octets.Bytes(), f),
    a,
    Lines.cut.of_left(f),
    Lists.List.fork_left(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  )

# a cut gives back the new lines
law Lines.cut_right:
  for +a: List<&2, Octets.Bytes()>
  for +b: List<&2, Octets.Bytes()>
  {Cut.right(Lines.cut(a, b)) == b: List<&2, Octets.Bytes()>}

def Lines.cut_right(a, b):
  +f = Lists.List.fork(~Octets.Bytes(), ~Octets.Bytes.is_eq, a, b)
  Equal.trans(
    List<&2, Octets.Bytes()>,
    Cut.right(Lines.cut.of(f)),
    Lists.Fork.right(Octets.Bytes(), f),
    b,
    Lines.cut.of_right(f),
    Lists.List.fork_right(~Octets.Bytes(), ~Octets.Bytes.is_eq, ~Octets.Bytes.is_eq_sound, a, b)
  )

# the lines a after a patch: keep the first keep lines, drop the next drop, and
# put the lines put in their place
def Lines.apply(keep: Nat, a: List<&2, Octets.Bytes()>, drop: Nat, put: List<&2, Octets.Bytes()>) -> List<&2, Octets.Bytes()>:
  match keep a:
    case 0n x:
      List.append(&2, Octets.Bytes(), put, List.drop(&2, Octets.Bytes(), x, drop))
    case 1n+k Nil{}:
      put
    case 1n+k Con{l, r}:
      l <> Lines.apply(k, r, drop, put)

# applying the patch of a cut to its old lines gives its new lines
def Lines.apply_cut(
  s: List<&2, Octets.Bytes()>,
  +o: List<&2, Octets.Bytes()>,
  n: List<&2, Octets.Bytes()>,
  e: List<&2, Octets.Bytes()>
) -> {
  Lines.apply(List.length(&2, Octets.Bytes(), s), Cut.left(Cut{s, o, n, e}), List.length(&2, Octets.Bytes(), o), n)
    == Cut.right(Cut{s, o, n, e}): List<&2, Octets.Bytes()>
}:
  match s:
    case Nil{}:
      %Equal.sym(
        List<&2, Octets.Bytes()>,
        List.drop(&2, Octets.Bytes(), List.append(&2, Octets.Bytes(), o, e), List.length(&2, Octets.Bytes(), o)),
        e,
        Lists.List.drop_after_append(Octets.Bytes(), o, e)
      ) :
        {List.append(&2, Octets.Bytes(), n, _) == List.append(&2, Octets.Bytes(), n, e): List<&2, Octets.Bytes()>}
      {==}
    case Con{l, r}:
      %Equal.sym(
        List<&2, Octets.Bytes()>,
        Lines.apply(List.length(&2, Octets.Bytes(), r), Cut.left(Cut{r, o, n, e}), List.length(&2, Octets.Bytes(), o), n),
        Cut.right(Cut{r, o, n, e}),
        Lines.apply_cut(r, o, n, e)
      ) :
        {l <> _ == l <> Cut.right(Cut{r, o, n, e}): List<&2, Octets.Bytes()>}
      {==}

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
def Lines.bytes_of(s: Octets.Bytes() & List<&2, Octets.Bytes()>) -> {Lines.bytes(Lines.list.of(s)) == Lines.join.of(s): Octets.Bytes()}:
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
# content
type Patch is Data:
  Patch.Lines{keep: Nat, drop: Nat, put: List<&2, Octets.Bytes()>}
  Patch.Whole{bytes: Octets.Bytes()}

# x is not 0
def Format.not_nul(x: U32) -> Bool:
  Bool.not(U32.is_eq(x, 0))

# b is text: no byte of it is 0
def Format.is_text(b: Octets.Bytes()) -> Bool:
  List.all(~&2, ~U32, ~Format.not_nul, b)

# the patch of the lines of a cut
def Lines.patch(c: Cut) -> Patch:
  match c:
    case Cut{s, o, n, e}:
      Patch.Lines{List.length(&2, Octets.Bytes(), s), List.length(&2, Octets.Bytes(), o), n}

# the patch from a to b, as lines when both are text (text)
def Format.diff.by(text: Bool, +a: Octets.Bytes(), b: Octets.Bytes()) -> Patch:
  match text:
    case True{}:
      Lines.patch(Lines.cut(Lines.list(a), Lines.list(b)))
    case False{}:
      Patch.Whole{b}

# the patch from a to b
def Format.diff(+a: Octets.Bytes(), +b: Octets.Bytes()) -> Patch:
  Format.diff.by(Bool.and(Format.is_text(a), Format.is_text(b)), a, b)

# a after the patch p
def Format.apply(a: Octets.Bytes(), p: Patch) -> Octets.Bytes():
  match p:
    case Patch.Lines{k, d, put}:
      Lines.bytes(Lines.apply(k, Lines.list(a), d, put))
    case Patch.Whole{x}:
      x

# the patch of a cut c of the lines of a, applied to a, gives the bytes of the
# new lines lb of c
def Format.apply_patch(
  c: Cut,
  +a: Octets.Bytes(),
  +lb: List<&2, Octets.Bytes()>,
  hl: {Cut.left(c) == Lines.list(a): List<&2, Octets.Bytes()>},
  hr: {Cut.right(c) == lb: List<&2, Octets.Bytes()>}
) -> {Format.apply(a, Lines.patch(c)) == Lines.bytes(lb): Octets.Bytes()}:
  match c:
    case Cut{+s, +o, +n, +e}:
      Equal.cong(
        List<&2, Octets.Bytes()>,
        Octets.Bytes(),
        z => Lines.bytes(z),
        Lines.apply(List.length(&2, Octets.Bytes(), s), Lines.list(a), List.length(&2, Octets.Bytes(), o), n),
        lb,
        %hl : {Lines.apply(List.length(&2, Octets.Bytes(), s), _, List.length(&2, Octets.Bytes(), o), n) == lb: List<&2, Octets.Bytes()>}
        %hr : {Lines.apply(List.length(&2, Octets.Bytes(), s), Cut.left(Cut{s, o, n, e}), List.length(&2, Octets.Bytes(), o), n) == _: List<&2, Octets.Bytes()>}
        Lines.apply_cut(s, o, n, e)
      )

# Format.apply_diff, by whether both are text (text)
def Format.apply_diff.by(text: Bool, +a: Octets.Bytes(), +b: Octets.Bytes()) -> {Format.apply(a, Format.diff.by(text, a, b)) == b: Octets.Bytes()}:
  match text:
    case True{}:
      +la = Lines.list(a)
      +lb = Lines.list(b)
      Equal.trans(
        Octets.Bytes(),
        Format.apply(a, Lines.patch(Lines.cut(la, lb))),
        Lines.bytes(lb),
        b,
        Format.apply_patch(Lines.cut(la, lb), a, lb, Lines.cut_left(la, lb), Lines.cut_right(la, lb)),
        Lines.bytes_list(b)
      )
    case False{}:
      {==}

# the patch from a to b, applied to a, gives b
law Format.apply_diff:
  for +a: Octets.Bytes()
  for +b: Octets.Bytes()
  {Format.apply(a, Format.diff(a, b)) == b: Octets.Bytes()}

def Format.apply_diff(a, b):
  Format.apply_diff.by(Bool.and(Format.is_text(a), Format.is_text(b)), a, b)

# Merges
# ------
# A merge of x and y, two changes of b. When only one side changed, or both
# made the same change, the merge is that change (Format.merge_*). When both
# changed text, each by one hunk of lines, the hunks merge when one ends before
# the other starts. Anything else clashes.

# a merge: its bytes, or a clash
type Merged is Data:
  Merged.Clean{bytes: Octets.Bytes()}
  Merged.Clash{}

# the lines lb after two patches, x's first when it ends before y's starts
# (x_first), y's first when it ends before x's starts (y_first)
def Format.merge.order(
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
      Merged.Clean{Lines.bytes(Lines.apply(kx, Lines.apply(ky, lb, dy, ny), dx, nx))}
    case False{} True{}:
      Merged.Clean{Lines.bytes(Lines.apply(ky, Lines.apply(kx, lb, dx, nx), dy, ny))}
    case False{} False{}:
      Merged.Clash{}

# the merge of the cuts cx and cy of the lines lb
def Format.merge.cuts(lb: List<&2, Octets.Bytes()>, cx: Cut, cy: Cut) -> Merged:
  match cx cy:
    case Cut{sx, ox, nx, ex} Cut{sy, oy, ny, ey}:
      +kx = List.length(&2, Octets.Bytes(), sx)
      +dx = List.length(&2, Octets.Bytes(), ox)
      +ky = List.length(&2, Octets.Bytes(), sy)
      +dy = List.length(&2, Octets.Bytes(), oy)
      Format.merge.order(Nat.is_lt(Nat.add(kx, dx), ky), Nat.is_lt(Nat.add(ky, dy), kx), lb, kx, dx, nx, ky, dy, ny)

# the merge of two text changes, by their lines
def Format.merge.lines(b: Octets.Bytes(), x: Octets.Bytes(), y: Octets.Bytes()) -> Merged:
  +lb = Lines.list(b)
  Format.merge.cuts(lb, Lines.cut(lb, Lines.list(x)), Lines.cut(lb, Lines.list(y)))

# the merge of two different changes, as lines when all three are text (text)
def Format.merge.text(text: Bool, b: Octets.Bytes(), x: Octets.Bytes(), y: Octets.Bytes()) -> Merged:
  match text:
    case True{}:
      Format.merge.lines(b, x, y)
    case False{}:
      Merged.Clash{}

# the merge when x and y are the same change or not (held)
def Format.merge.same(held: Bool, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  match held:
    case True{}:
      Merged.Clean{x}
    case False{}:
      Format.merge.text(Bool.and(Format.is_text(b), Bool.and(Format.is_text(x), Format.is_text(y))), b, x, y)

# the merge when y is b or not (held)
def Format.merge.right(held: Bool, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  match held:
    case True{}:
      Merged.Clean{x}
    case False{}:
      Format.merge.same(Octets.Bytes.is_eq(x, y), b, x, y)

# the merge when x is b or not (held)
def Format.merge.left(held: Bool, +b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  match held:
    case True{}:
      Merged.Clean{y}
    case False{}:
      Format.merge.right(Octets.Bytes.is_eq(y, b), b, x, y)

# the merge of x and y, two changes of b
def Format.merge(+b: Octets.Bytes(), +x: Octets.Bytes(), +y: Octets.Bytes()) -> Merged:
  Format.merge.left(Octets.Bytes.is_eq(x, b), b, x, y)

# Format.merge_left_only once x is known to be b or not (held)
def Format.merge_left_only.at(
  held: Bool,
  +b: Octets.Bytes(),
  +x: Octets.Bytes(),
  e: {Octets.Bytes.is_eq(x, b) == held: Bool}
) -> {Format.merge.left(held, b, x, b) == Merged.Clean{x}: Merged}:
  match held:
    case True{}:
      %Equal.sym(Octets.Bytes(), x, b, Octets.Bytes.is_eq_sound(x, b)(e)) : {Merged.Clean{b} == Merged.Clean{_}: Merged}
      {==}
    case False{}:
      %Equal.sym(Bool, Octets.Bytes.is_eq(b, b), True{}, Octets.Bytes.is_eq_refl(b)) :
        {Format.merge.right(_, b, x, b) == Merged.Clean{x}: Merged}
      {==}

# when only x changed b, the merge is x
law Format.merge_left_only:
  for +b: Octets.Bytes()
  for +x: Octets.Bytes()
  {Format.merge(b, x, b) == Merged.Clean{x}: Merged}

def Format.merge_left_only(b, x):
  Format.merge_left_only.at(Octets.Bytes.is_eq(x, b), b, x, {==})

# when only y changed b, the merge is y
law Format.merge_right_only:
  for +b: Octets.Bytes()
  for +y: Octets.Bytes()
  {Format.merge(b, b, y) == Merged.Clean{y}: Merged}

def Format.merge_right_only(b, y):
  %Equal.sym(Bool, Octets.Bytes.is_eq(b, b), True{}, Octets.Bytes.is_eq_refl(b)) :
    {Format.merge.left(_, b, b, y) == Merged.Clean{y}: Merged}
  {==}

# Format.merge_same once x is known to be b or not (held)
def Format.merge_same.at(
  held: Bool,
  +b: Octets.Bytes(),
  +x: Octets.Bytes(),
  e: {Octets.Bytes.is_eq(x, b) == held: Bool}
) -> {Format.merge.left(held, b, x, x) == Merged.Clean{x}: Merged}:
  match held:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Octets.Bytes.is_eq(x, b), False{}, e) :
        {Format.merge.right(_, b, x, x) == Merged.Clean{x}: Merged}
      %Equal.sym(Bool, Octets.Bytes.is_eq(x, x), True{}, Octets.Bytes.is_eq_refl(x)) :
        {Format.merge.same(_, b, x, x) == Merged.Clean{x}: Merged}
      {==}

# when both made the same change, the merge is that change
law Format.merge_same:
  for +b: Octets.Bytes()
  for +x: Octets.Bytes()
  {Format.merge(b, x, x) == Merged.Clean{x}: Merged}

def Format.merge_same(b, x):
  Format.merge_same.at(Octets.Bytes.is_eq(x, b), b, x, {==})

# Changes
# -------
# What a patch does, part by part, for a reader.

# a part of a resource: its kind (line, content), where it is (a line counts
# from 1; a whole content is at 0), and its bytes
type Item is Data:
  Item{kind: String, place: Nat, bytes: Octets.Bytes()}

# a part that a patch added or removed
type Change is Data:
  Change.Added{item: Item}
  Change.Removed{item: Item}

# the lines ls as the changes that make (c), counted from the line at
def Lines.changes(~make: Item -> Change, ls: List<&2, Octets.Bytes()>, +at: Nat) -> List<&2, Change>:
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      make(Item{"line", at, l}) <> Lines.changes(~make, r, 1n+at)

# a removed part
def Change.removed(i: Item) -> Change:
  Change.Removed{i}

# an added part
def Change.added(i: Item) -> Change:
  Change.Added{i}

# the changes of a whole content from a to b, none when they are the same
# (held)
def Format.changes.whole(held: Bool, a: Octets.Bytes(), b: Octets.Bytes()) -> List<&2, Change>:
  match held:
    case True{}:
      []
    case False{}:
      [Change.Removed{Item{"content", 0n, a}}, Change.Added{Item{"content", 0n, b}}]

# the changes of the patch p of a
def Format.changes.of(+a: Octets.Bytes(), p: Patch) -> List<&2, Change>:
  match p:
    case Patch.Lines{+k, +d, put}:
      List.append(
        &2,
        Change,
        Lines.changes(~Change.removed, List.take(&2, Octets.Bytes(), List.drop(&2, Octets.Bytes(), Lines.list(a), k), d), 1n+k),
        Lines.changes(~Change.added, put, 1n+k)
      )
    case Patch.Whole{+x}:
      Format.changes.whole(Octets.Bytes.is_eq(a, x), a, x)

# what changed from a to b, part by part
def Format.changes(+a: Octets.Bytes(), +b: Octets.Bytes()) -> List<&2, Change>:
  Format.changes.of(a, Format.diff(a, b))
