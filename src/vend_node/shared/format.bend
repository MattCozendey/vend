import Base
import ../../resource/formats.bend as Formats
import ../../resource/resources.bend as Resources
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/text.bend as Texts

# Formats of a Vend Node
# ----------------------
# The words of a resource are read in the format of its path (Formats.Format.guess):
# lines for text, one whole part for what is not text, the pieces of a nested
# format in their own format at any depth, and blocks (a function, a type) for
# code. Items, diffs and merges follow that format.

# Lines
# -----

# the lines ls of some words after the word c, by whether c ends a line (nl)
def Lines.after.put(nl: Bool, c: U32, ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match nl ls:
    case True{} r:
      [c] <> r
    case False{} Nil{}:
      [[c]]
    case False{} Con{l, t}:
      (c <> l) <> t

# the lines of the words ws, each with the newline (10) that ends it
def Lines.after(ws: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ws:
    case Nil{}:
      []
    case Con{+c, r}:
      Lines.after.put(U32.is_eq(c, 10), c, Lines.after(r))

# the lines after a word, put together, are the word and then the lines
def Lines.after.put_whole(
  nl: Bool,
  c: U32,
  ls: List<&2, List<&2, U32>>
) -> {
  List.concat(&2, U32, Lines.after.put(nl, c, ls)) == c <> List.concat(&2, U32, ls): List<&2, U32>
}:
  match nl ls:
    case True{} r:
      {==}
    case False{} Nil{}:
      {==}
    case False{} Con{l, t}:
      {==}

# the lines of ws, put together, are ws
def Lines.after_whole(
  ws: List<&2, U32>
) -> {List.concat(&2, U32, Lines.after(ws)) == ws: List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      %Lines.after_whole(
        r
      ): {
        List.concat(
          &2,
          U32,
          Lines.after.put(U32.is_eq(c, 10), c, Lines.after(r))
        )
          == c
          <> _: List<&2, U32>
      }
      Lines.after.put_whole(U32.is_eq(c, 10), c, Lines.after(r))

# the items of the words ws when they are text or not (text): lines, or one
# whole part
def Lines.items.by(text: Bool, ws: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match text:
    case True{}:
      Lines.after(ws)
    case False{}:
      [ws]

# the items of some text or not, put together, are its words
def Lines.items.by_whole(
  text: Bool,
  ws: List<&2, U32>
) -> {List.concat(&2, U32, Lines.items.by(text, ws)) == ws: List<&2, U32>}:
  match text:
    case True{}:
      Lines.after_whole(ws)
    case False{}:
      Shared.List.append_nil(U32, ws)

# the items of the words ws in the leaf format k: lines for text, one whole
# part for what is not text (it holds a 0) and for a format with no lines
def Leaf.items(k: Formats.Leaf, +ws: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match k:
    case Formats.Leaf.Lines{}:
      Lines.items.by(Formats.Plain.is_text(ws), ws)
    case Formats.Leaf.Whole{}:
      [ws]
    case Formats.Leaf.Module{}:
      [ws]

# the items of a leaf, put together, are its words
def Leaf.items_whole(
  k: Formats.Leaf,
  +ws: List<&2, U32>
) -> {List.concat(&2, U32, Leaf.items(k, ws)) == ws: List<&2, U32>}:
  match k:
    case Formats.Leaf.Lines{}:
      Lines.items.by_whole(Formats.Plain.is_text(ws), ws)
    case Formats.Leaf.Whole{}:
      Shared.List.append_nil(U32, ws)
    case Formats.Leaf.Module{}:
      Shared.List.append_nil(U32, ws)

# Blocks
# ------
# Code is read without running it: a block (a function, a type, an import)
# starts at a line that starts at the margin with a word that is not a closing
# bracket, and holds the lines up to the next such line.

# the word x does not start a block: a blank, a line end or a closing bracket
def Block.inside(+x: U32) -> Bool:
  Bool.or(
    Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9)),
    Bool.or(
      Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13)),
      Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 41), U32.is_eq(x, 93)))
    )
  )

# the item l starts a block
def Block.starts(l: List<&2, U32>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.not(Block.inside(x))

# the blocks of the item l and then the item h and the blocks t, by whether h
# starts a block (starts)
def Blocks.put.on(
  starts: Bool,
  l: List<&2, U32>,
  h: List<&2, U32>,
  t: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match starts:
    case True{}:
      l <> h <> t
    case False{}:
      List.append(&2, U32, l, h) <> t

# the blocks of the item l and then the blocks g
def Blocks.put(l: List<&2, U32>, g: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match g:
    case Nil{}:
      [l]
    case Con{+h, t}:
      Blocks.put.on(Block.starts(h), l, h, t)

# the blocks of the items ls: each item that starts no block joins the one
# before it
def Blocks.group(ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      []
    case Con{l, r}:
      Blocks.put(l, Blocks.group(r))

# Blocks.put.on loses no word
def Blocks.put.on_whole(
  starts: Bool,
  l: List<&2, U32>,
  h: List<&2, U32>,
  t: List<&2, List<&2, U32>>
) -> {
  List.concat(
    &2,
    U32,
    Blocks.put.on(starts, l, h, t)
  )
    == List.append(&2, U32, l, List.append(&2, U32, h, List.concat(&2, U32, t))): List<&2, U32>
}:
  match starts:
    case True{}:
      {==}
    case False{}:
      Shared.List.append_assoc(U32, l, h, List.concat(&2, U32, t))

# Blocks.put loses no word
def Blocks.put_whole(
  l: List<&2, U32>,
  g: List<&2, List<&2, U32>>
) -> {
  List.concat(
    &2,
    U32,
    Blocks.put(l, g)
  )
    == List.append(&2, U32, l, List.concat(&2, U32, g)): List<&2, U32>
}:
  match g:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Blocks.put.on_whole(Block.starts(h), l, h, t)

# the blocks of some items, put together, are the items put together
def Blocks.group_whole(
  ls: List<&2, List<&2, U32>>
) -> {List.concat(&2, U32, Blocks.group(ls)) == List.concat(&2, U32, ls): List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +r}:
      %Blocks.group_whole(
        r
      ): {
        List.concat(
          &2,
          U32,
          Blocks.put(l, Blocks.group(r))
        )
          == List.append(&2, U32, l, _): List<&2, U32>
      }
      Blocks.put_whole(l, Blocks.group(r))

# Items
# -----

# the pieces of the words ws in the format f, when it is an embedding (under
# any language): none for a leaf
def Pieces.of(f: Formats.Format, +ws: List<&2, U32>) -> List<&2, Formats.Piece>:
  match f:
    case Formats.Format.Leaf{k}:
      []
    case Formats.Format.Embed{o, op, cl, i}:
      Formats.Embed.split(op, cl, ws)
    case Formats.Format.Code{b, r, im}:
      Pieces.of(b, ws)

# the closing marker cl of a region, as an item, when it has one (closed)
def Items.close(closed: Bool, cl: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match closed:
    case True{}:
      [cl]
    case False{}:
      []

# the items of the words ws in the format f, whose pieces are ps (Pieces.of):
# the items of a leaf; the blocks of a language; and for an embedding the
# items of each piece in its own format, with each marker as an item
def Items.go(
  +f: Formats.Format,
  ps: List<&2, Formats.Piece>,
  +ws: List<&2, U32>
) -> List<&2, List<&2, U32>>:
  match f ps:
    case Formats.Format.Leaf{k} q:
      Leaf.items(k, ws)
    case Formats.Format.Code{b, r, im} q:
      Blocks.group(Items.go(b, Pieces.of(b, ws), ws))
    case Formats.Format.Embed{o, op, cl, i} Nil{}:
      []
    case Formats.Format.Embed{o, op, cl, i} Con{Formats.Piece.Text{+t}, rest}:
      List.append(&2, List<&2, U32>, Items.go(o, Pieces.of(o, t), t), Items.go(f, rest, ws))
    case Formats.Format.Embed{o, op, cl, i} Con{Formats.Piece.Region{+c, closed}, rest}:
      op
        <> List.append(
          &2,
          List<&2, U32>,
          Items.go(i, Pieces.of(i, c), c),
          List.append(&2, List<&2, U32>, Items.close(closed, cl), Items.go(f, rest, ws))
        )

# the words that the items of Items.go hold: ws, or for an embedding its
# pieces ps, joined
def Items.sum(f: Formats.Format, ps: List<&2, Formats.Piece>, ws: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Formats.Format.Leaf{k}:
      ws
    case Formats.Format.Embed{o, op, cl, i}:
      Formats.Embed.join(op, cl, ps)
    case Formats.Format.Code{b, r, im}:
      ws

# the pieces of ws in f hold the words ws
def Pieces.of_whole(
  f: Formats.Format,
  +ws: List<&2, U32>
) -> {Items.sum(f, Pieces.of(f, ws), ws) == ws: List<&2, U32>}:
  match f:
    case Formats.Format.Leaf{k}:
      {==}
    case Formats.Format.Embed{o, op, cl, i}:
      Formats.Embed.join_split(op, cl, ws)
    case Formats.Format.Code{b, r, im}:
      {==}

# two lists of items one after the other hold the words of each
def Items.two_whole(
  +xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>,
  -a: List<&2, U32>,
  -b: List<&2, U32>,
  ea: {List.concat(&2, U32, xs) == a: List<&2, U32>},
  eb: {List.concat(&2, U32, ys) == b: List<&2, U32>}
) -> {
  List.concat(
    &2,
    U32,
    List.append(&2, List<&2, U32>, xs, ys)
  )
    == List.append(&2, U32, a, b): List<&2, U32>
}:
  %ea: {
    List.concat(
      &2,
      U32,
      List.append(&2, List<&2, U32>, xs, ys)
    )
      == List.append(&2, U32, _, b): List<&2, U32>
  }
  %eb: {
    List.concat(
      &2,
      U32,
      List.append(&2, List<&2, U32>, xs, ys)
    )
      == List.append(&2, U32, List.concat(&2, U32, xs), _): List<&2, U32>
  }
  Shared.List.concat_append(U32, xs, ys)

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# the items of Items.go, put together, are the words that it reads
def Items.go_whole(
  +f: Formats.Format,
  ps: List<&2, Formats.Piece>,
  +ws: List<&2, U32>
) -> {List.concat(&2, U32, Items.go(f, ps, ws)) == Items.sum(f, ps, ws): List<&2, U32>}:
  match f ps:
    case Formats.Format.Leaf{k} q:
      Leaf.items_whole(k, ws)
    case Formats.Format.Code{+b, r, im} q:
      Equal.trans(
        List<&2, U32>,
        List.concat(&2, U32, Blocks.group(Items.go(b, Pieces.of(b, ws), ws))),
        List.concat(&2, U32, Items.go(b, Pieces.of(b, ws), ws)),
        ws,
        Blocks.group_whole(Items.go(b, Pieces.of(b, ws), ws)),
        Equal.trans(
          List<&2, U32>,
          List.concat(&2, U32, Items.go(b, Pieces.of(b, ws), ws)),
          Items.sum(b, Pieces.of(b, ws), ws),
          ws,
          Items.go_whole(b, Pieces.of(b, ws), ws),
          Pieces.of_whole(b, ws)
        )
      )
    case Formats.Format.Embed{o, op, cl, i} Nil{}:
      {==}
    case Formats.Format.Embed{+o, +op, +cl, +i} Con{Formats.Piece.Text{+t}, +rest}:
      Items.two_whole(
        Items.go(o, Pieces.of(o, t), t),
        Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws),
        t,
        Formats.Embed.join(op, cl, rest),
        Equal.trans(
          List<&2, U32>,
          List.concat(&2, U32, Items.go(o, Pieces.of(o, t), t)),
          Items.sum(o, Pieces.of(o, t), t),
          t,
          Items.go_whole(o, Pieces.of(o, t), t),
          Pieces.of_whole(o, t)
        ),
        Items.go_whole(f, rest, ws)
      )
    case Formats.Format.Embed{+o, +op, +cl, +i} Con{Formats.Piece.Region{+c, True{}}, +rest}:
      Equal.cong(
        List<&2, U32>,
        List<&2, U32>,
        z => List.append(&2, U32, op, z),
        List.concat(
          &2,
          U32,
          List.append(
            &2,
            List<&2, U32>,
            Items.go(i, Pieces.of(i, c), c),
            cl <> Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws)
          )
        ),
        List.append(&2, U32, c, List.append(&2, U32, cl, Formats.Embed.join(op, cl, rest))),
        Items.two_whole(
          Items.go(i, Pieces.of(i, c), c),
          cl <> Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws),
          c,
          List.append(&2, U32, cl, Formats.Embed.join(op, cl, rest)),
          Equal.trans(
            List<&2, U32>,
            List.concat(&2, U32, Items.go(i, Pieces.of(i, c), c)),
            Items.sum(i, Pieces.of(i, c), c),
            c,
            Items.go_whole(i, Pieces.of(i, c), c),
            Pieces.of_whole(i, c)
          ),
          Equal.cong(
            List<&2, U32>,
            List<&2, U32>,
            z => List.append(&2, U32, cl, z),
            List.concat(&2, U32, Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws)),
            Formats.Embed.join(op, cl, rest),
            Items.go_whole(f, rest, ws)
          )
        )
      )
    case Formats.Format.Embed{+o, +op, +cl, +i} Con{Formats.Piece.Region{+c, False{}}, +rest}:
      Equal.cong(
        List<&2, U32>,
        List<&2, U32>,
        z => List.append(&2, U32, op, z),
        List.concat(
          &2,
          U32,
          List.append(
            &2,
            List<&2, U32>,
            Items.go(i, Pieces.of(i, c), c),
            Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws)
          )
        ),
        List.append(&2, U32, c, Formats.Embed.join(op, cl, rest)),
        Items.two_whole(
          Items.go(i, Pieces.of(i, c), c),
          Items.go(Formats.Format.Embed{o, op, cl, i}, rest, ws),
          c,
          Formats.Embed.join(op, cl, rest),
          Equal.trans(
            List<&2, U32>,
            List.concat(&2, U32, Items.go(i, Pieces.of(i, c), c)),
            Items.sum(i, Pieces.of(i, c), c),
            c,
            Items.go_whole(i, Pieces.of(i, c), c),
            Pieces.of_whole(i, c)
          ),
          Items.go_whole(f, rest, ws)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the items that the words ws of the resource at the path p are read as, in
# its format
def Format.items(p: String, ws: List<&2, U32>) -> List<&2, List<&2, U32>>:
  +ws = ws
  +f = Formats.Format.guess(p)
  Items.go(f, Pieces.of(f, ws), ws)

# the items of a resource, put together, are its words
def Format.items_whole(
  p: String,
  ws: List<&2, U32>
) -> {List.concat(&2, U32, Format.items(p, ws)) == ws: List<&2, U32>}:
  +ws = ws
  +f = Formats.Format.guess(p)
  Equal.trans(
    List<&2, U32>,
    List.concat(&2, U32, Items.go(f, Pieces.of(f, ws), ws)),
    Items.sum(f, Pieces.of(f, ws), ws),
    ws,
    Items.go_whole(f, Pieces.of(f, ws), ws),
    Pieces.of_whole(f, ws)
  )

# Diffs
# -----
# A diff is hunks over the items of the format, each after the last: keep
# some items, drop some, put some in their place (Formats.Hunk, found by
# Formats.Lines.diff with the fewest items dropped and put). Its size follows
# the size of the change, not of the content.

# a change from one content to another
def Diff() -> Data:
  List<&2, Formats.Hunk>

# the hunks hs fit n items: each keeps and drops items that are there
def Hunks.fit(hs: List<&2, Formats.Hunk>, +n: Nat) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{Formats.Hunk{k, d, put}, rest}:
      +u = Nat.add(k, d)
      Bool.and(Nat.is_le(u, n), Hunks.fit(rest, Nat.sub(n, u)))

# the hunks d from the items a to the items b when they fit a, else the one
# hunk that drops all of a and puts b
def Diff.check(
  +d: List<&2, Formats.Hunk>,
  +a: List<&2, List<&2, U32>>,
  b: List<&2, List<&2, U32>>
) -> List<&2, Formats.Hunk>:
  Shared.Bool.when(
    List<&2, Formats.Hunk>,
    Hunks.fit(d, List.length(&2, List<&2, U32>, a)),
    u => d,
    u => [Formats.Hunk{0n, List.length(&2, List<&2, U32>, a), b}]
  )

# the words of the items a after the hunks x, when they fit (fits)
def Diff.apply.if(
  fits: Bool,
  x: List<&2, Formats.Hunk>,
  a: List<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, U32>>:
  match fits:
    case True{}:
      Some{List.concat(&2, U32, Formats.Lines.apply.all(x, a))}
    case False{}:
      None{}

# the words of the items a after the hunks x (none: x does not fit a)
def Diff.apply(+x: List<&2, Formats.Hunk>, +a: List<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  Diff.apply.if(Hunks.fit(x, List.length(&2, List<&2, U32>, a)), x, a)

# the change from a to b of the resource at p, in its format
def Format.diff(p: String, a: List<&2, U32>, b: List<&2, U32>) -> Diff():
  +p = p
  +ia = Format.items(p, a)
  +ib = Format.items(p, b)
  Diff.check(Formats.Lines.diff(ia, ib), ia, ib)

# a after the change x, in the format of the resource at p (none: x does not
# apply to a)
def Format.apply(p: String, a: List<&2, U32>, x: Diff()) -> Maybe<&2, List<&2, U32>>:
  Diff.apply(x, Format.items(p, a))

# hunks that fit apply
def Diff.apply.if_fits(
  fits: Bool,
  x: List<&2, Formats.Hunk>,
  a: List<&2, List<&2, U32>>,
  e: {fits == True{}: Bool}
) -> {
  Diff.apply.if(
    fits,
    x,
    a
  )
    == Some{List.concat(&2, U32, Formats.Lines.apply.all(x, a))}: Maybe<&2, List<&2, U32>>
}:
  match fits:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(
        {
          None{}
            == Some{List.concat(&2, U32, Formats.Lines.apply.all(x, a))}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(e)
      )

# a list without all its elements is empty
def List.drop_all(
  -A: Data,
  xs: List<&2, A>
) -> {List.drop(&2, A, xs, List.length(&2, A, xs)) == []: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      List.drop_all(A, r)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# the one hunk that drops all of a and puts b fits a
def Diff.whole_fits(
  n: Nat,
  b: List<&2, List<&2, U32>>
) -> {Hunks.fit([Formats.Hunk{0n, n, b}], n) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Nat.is_le(n, n),
    True{},
    Shared.Nat.le_refl(n)
  ): {Bool.and(_, True{}) == True{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the one hunk that drops all of a and puts b makes b of a
def Diff.whole_apply(
  +a: List<&2, List<&2, U32>>,
  +b: List<&2, List<&2, U32>>
) -> {
  Formats.Lines.apply.all(
    [Formats.Hunk{0n, List.length(&2, List<&2, U32>, a), b}],
    a
  )
    == b: List<&2, List<&2, U32>>
}:
  Equal.trans(
    List<&2, List<&2, U32>>,
    Formats.Lines.apply.all([Formats.Hunk{0n, List.length(&2, List<&2, U32>, a), b}], a),
    List.append(
      &2,
      List<&2, U32>,
      b,
      List.drop(&2, List<&2, U32>, a, List.length(&2, List<&2, U32>, a))
    ),
    b,
    Formats.Lines.apply.all_one(0n, a, List.length(&2, List<&2, U32>, a), b),
    Equal.trans(
      List<&2, List<&2, U32>>,
      List.append(
        &2,
        List<&2, U32>,
        b,
        List.drop(&2, List<&2, U32>, a, List.length(&2, List<&2, U32>, a))
      ),
      List.append(&2, List<&2, U32>, b, []),
      b,
      Equal.cong(
        List<&2, List<&2, U32>>,
        List<&2, List<&2, U32>>,
        z => List.append(&2, List<&2, U32>, b, z),
        List.drop(&2, List<&2, U32>, a, List.length(&2, List<&2, U32>, a)),
        [],
        List.drop_all(List<&2, U32>, a)
      ),
      Shared.List.append_nil(List<&2, U32>, b)
    )
  )

# hunks that fit a and make the items b of it apply to a and give the words of b
def Diff.apply_fits(
  +x: List<&2, Formats.Hunk>,
  +a: List<&2, List<&2, U32>>,
  +b: List<&2, List<&2, U32>>,
  ef: {Hunks.fit(x, List.length(&2, List<&2, U32>, a)) == True{}: Bool},
  eb: {Formats.Lines.apply.all(x, a) == b: List<&2, List<&2, U32>>}
) -> {Diff.apply(x, a) == Some{List.concat(&2, U32, b)}: Maybe<&2, List<&2, U32>>}:
  %eb: {Diff.apply(x, a) == Some{List.concat(&2, U32, _)}: Maybe<&2, List<&2, U32>>}
  Diff.apply.if_fits(Hunks.fit(x, List.length(&2, List<&2, U32>, a)), x, a, ef)

# checked hunks that make the items b of a apply to a and give the words of b
def Diff.apply_check(
  +d: List<&2, Formats.Hunk>,
  +a: List<&2, List<&2, U32>>,
  +b: List<&2, List<&2, U32>>,
  h: {Formats.Lines.apply.all(d, a) == b: List<&2, List<&2, U32>>}
) -> {
  Diff.apply(Diff.check(d, a, b), a) == Some{List.concat(&2, U32, b)}: Maybe<&2, List<&2, U32>>
}:
  Shared.Bool.when_cases(
    List<&2, Formats.Hunk>,
    r => {Diff.apply(r, a) == Some{List.concat(&2, U32, b)}: Maybe<&2, List<&2, U32>>},
    Hunks.fit(d, List.length(&2, List<&2, U32>, a)),
    u => d,
    u => [Formats.Hunk{0n, List.length(&2, List<&2, U32>, a), b}],
    e => Diff.apply_fits(d, a, b, e, h),
    e => Diff.apply_fits(
      [Formats.Hunk{0n, List.length(&2, List<&2, U32>, a), b}],
      a,
      b,
      Diff.whole_fits(List.length(&2, List<&2, U32>, a), b),
      Diff.whole_apply(a, b)
    )
  )

# the checked diff from the items a to the items b, whose words are ws, applied
# to a, gives ws
def Diff.apply_diff(
  +ia: List<&2, List<&2, U32>>,
  +ib: List<&2, List<&2, U32>>,
  -ws: List<&2, U32>,
  e: {List.concat(&2, U32, ib) == ws: List<&2, U32>}
) -> {
  Diff.apply(
    Diff.check(Formats.Lines.diff(ia, ib), ia, ib),
    ia
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  %e:
    {
      Diff.apply(
        Diff.check(Formats.Lines.diff(ia, ib), ia, ib),
        ia
      )
        == Some{_}: Maybe<&2, List<&2, U32>>
    }
  Diff.apply_check(Formats.Lines.diff(ia, ib), ia, ib, Formats.Lines.apply_diff(ia, ib))

# a diff applies: a after the diff from a to b is b
def Format.apply_diff(
  p: String,
  a: List<&2, U32>,
  b: List<&2, U32>
) -> {Format.apply(p, a, Format.diff(p, a, b)) == Some{b}: Maybe<&2, List<&2, U32>>}:
  +p = p
  +b = b
  Diff.apply_diff(Format.items(p, a), Format.items(p, b), b, Format.items_whole(p, b))

# Merges
# ------
# A merge first chooses as every three-way merge does: theirs when ours is
# the base, ours when theirs is the base or both are the same. Only two
# different changes are merged in the format (Formats.Format.merge: piece by
# piece in a nested format, hunk by hunk over the lines), and they clash when
# both changed the same part differently, or one removed the resource.

# a and b are the same content, or both no resource
def Content.same(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)

# a content is the same as itself
def Content.same_refl(a: Maybe<&2, List<&2, U32>>) -> {Content.same(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), x)

# contents that are the same are equal
def Content.same_sound(
  a: Maybe<&2, List<&2, U32>>,
  b: Maybe<&2, List<&2, U32>>
) -> {Content.same(a, b) == True{}: Bool} -> {a == b: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
    a,
    b
  )

# a merge of a format, as a content or a clash
def Merge.of(m: Formats.Merged) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case Formats.Merged.Clean{z}:
      Some{Some{z}}
    case Formats.Merged.Clash{}:
      None{}

# the merge of two different changes of base, in the format of the path p: of
# two contents, in the format (a base that is no resource is empty); a clash
# when a side removed the resource
def Merge.both(
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match ours theirs:
    case Some{x} Some{y}:
      Merge.of(
        Formats.Format.merge(
          Formats.Format.guess(p),
          Maybe.default(&2, List<&2, U32>, base, []),
          x,
          y
        )
      )
    case o t:
      None{}

# the merge, once it is known whether ours is the base (ob), theirs is the
# base (tb) and ours is theirs (ot)
def Merge.pick(
  ob: Bool,
  tb: Bool,
  ot: Bool,
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match ob tb ot:
    case True{} t s:
      Some{theirs}
    case False{} True{} s:
      Some{ours}
    case False{} False{} True{}:
      Some{ours}
    case False{} False{} False{}:
      Merge.both(p, base, ours, theirs)

# the merge of ours and theirs, two changes of base (none inside: no resource),
# in the format of the resource at p; nothing when they clash
def Format.merge(
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  +base = base
  +ours = ours
  +theirs = theirs
  Merge.pick(
    Content.same(ours, base),
    Content.same(theirs, base),
    Content.same(ours, theirs),
    p,
    base,
    ours,
    theirs
  )

# a merge whose ours is the base is theirs
def Merge.pick_theirs(
  ob: Bool,
  tb: Bool,
  ot: Bool,
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>,
  e: {ob == True{}: Bool}
) -> {
  Merge.pick(ob, tb, ot, p, base, ours, theirs) == Some{theirs}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match ob:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(
        {
          Merge.pick(
            False{},
            tb,
            ot,
            p,
            base,
            ours,
            theirs
          )
            == Some{theirs}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(e)
      )

# a merge whose theirs is the base is ours: when ours is the base too, theirs
# is ours (h)
def Merge.pick_ours(
  ob: Bool,
  tb: Bool,
  ot: Bool,
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>,
  e: {tb == True{}: Bool},
  h: {ob == True{}: Bool} -> {theirs == ours: Maybe<&2, List<&2, U32>>}
) -> {
  Merge.pick(ob, tb, ot, p, base, ours, theirs) == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match ob tb:
    case True{} t:
      Equal.cong(
        Maybe<&2, List<&2, U32>>,
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        z => Some{z},
        theirs,
        ours,
        h({==})
      )
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd(
        {
          Merge.pick(
            False{},
            False{},
            ot,
            p,
            base,
            ours,
            theirs
          )
            == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(e)
      )

# a merge of the same change on both sides is that change
def Merge.pick_same(
  ob: Bool,
  tb: Bool,
  ot: Bool,
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  both: Maybe<&2, List<&2, U32>>,
  e: {ot == True{}: Bool}
) -> {
  Merge.pick(ob, tb, ot, p, base, both, both) == Some{both}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match ob tb ot:
    case True{} t s:
      {==}
    case False{} True{} s:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      Empty.absurd(
        {
          Merge.pick(
            False{},
            False{},
            False{},
            p,
            base,
            both,
            both
          )
            == Some{both}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(e)
      )

# a merge never loses a change made on only one side: when ours did not
# change, it is theirs
def Format.merge_theirs(
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  theirs: Maybe<&2, List<&2, U32>>
) -> {Format.merge(p, base, base, theirs) == Some{theirs}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  +base = base
  +theirs = theirs
  Merge.pick_theirs(
    Content.same(base, base),
    Content.same(theirs, base),
    Content.same(base, theirs),
    p,
    base,
    base,
    theirs,
    Content.same_refl(base)
  )

# and when theirs did not change, it is ours
def Format.merge_ours(
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  ours: Maybe<&2, List<&2, U32>>
) -> {Format.merge(p, base, ours, base) == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  +base = base
  +ours = ours
  Merge.pick_ours(
    Content.same(ours, base),
    Content.same(base, base),
    Content.same(ours, base),
    p,
    base,
    ours,
    base,
    Content.same_refl(base),
    e => Equal.sym(Maybe<&2, List<&2, U32>>, ours, base, Content.same_sound(ours, base)(e))
  )

# and when both made the same change, it is that change
def Format.merge_same(
  p: String,
  base: Maybe<&2, List<&2, U32>>,
  both: Maybe<&2, List<&2, U32>>
) -> {Format.merge(p, base, both, both) == Some{both}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  +base = base
  +both = both
  Merge.pick_same(
    Content.same(both, base),
    Content.same(both, base),
    Content.same(both, both),
    p,
    base,
    both,
    Content.same_refl(both)
  )

# Imports
# -------
# The imports of a resource are read by the rule of its language, in each
# part that the language reads (Formats.Format.uses), each under the
# conditions that it sits in (C's #if, #ifdef, #ifndef, #else, #endif). A
# build is the names that it defines: an import counts when each of its
# conditions is taken in the build. Its target, as written, is found as the
# language finds it (Resources.Name.candidates): beside the resource, under
# each root, with each suffix; all the paths that it may be are given.

# the word x of a test stands between two names
def Test.is_gap(+x: U32) -> Bool:
  Bool.or(
    Bool.or(
      Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9)),
      Bool.or(U32.is_eq(x, 13), U32.is_eq(x, 10))
    ),
    Bool.or(
      Bool.or(U32.is_eq(x, 40), U32.is_eq(x, 41)),
      Bool.or(U32.is_eq(x, 33), Bool.or(U32.is_eq(x, 38), U32.is_eq(x, 124)))
    )
  )

# the names ns of some words after the word c, by whether c is a gap (gap)
def Test.names.put(gap: Bool, c: U32, ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match gap ns:
    case True{} r:
      [] <> r
    case False{} Nil{}:
      [[c]]
    case False{} Con{n, t}:
      (c <> n) <> t

# the names in the test t: its words between gaps (an empty one may be among
# them)
def Test.names(t: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match t:
    case Nil{}:
      []
    case Con{+c, r}:
      Test.names.put(Test.is_gap(c), c, Test.names(r))

# one of the names ns is a name of the build bs
def Test.named(ns: List<&2, List<&2, U32>>, +bs: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{n, rest}:
      List.any.if(
        u => Test.named(rest, bs),
        List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), bs, n)
      )

# the test t asks that a name is not defined: #ifndef, or !defined
def Test.negates(+t: List<&2, U32>) -> Bool:
  Shared.Bool.when(
    Bool,
    Formats.Bytes.starts([35, 105, 102, 110, 100, 101, 102], t),
    u => True{},
    u => Maybe.is_some(
      &2,
      Texts.Cut<List<&2, U32>>,
      Formats.Bytes.find([33, 100, 101, 102, 105, 110, 101, 100], t)
    )
  )

# the test t is taken in the build of the names bs: it names one of them, or
# asks that a name is not defined and names none
def Test.taken(+t: List<&2, U32>, bs: List<&2, List<&2, U32>>) -> Bool:
  Bool.not(Shared.Bool.is_eq(Test.named(Test.names(t), bs), Test.negates(t)))

# each of the conditions cs is taken in the build of the names bs: its test is
# taken in its first part, and not taken after its otherwise
def Conds.taken(cs: List<&2, Formats.Cond>, +bs: List<&2, List<&2, U32>>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{Formats.Cond{t, h}, rest}:
      List.all.if(u => Conds.taken(rest, bs), Shared.Bool.is_eq(Test.taken(t, bs), h))

# the words of each of the names bs
def Names.words(bs: List<&2, String>) -> List<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      Texts.Bytes.of_text(b) <> Names.words(rest)

# the paths of the names ns, then rest
def Names.paths(ns: List<&2, Resources.Name>, rest: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      rest
    case Con{n, more}:
      Resources.Name.path(n) <> Names.paths(more, rest)

# the paths that the imports xs of the resource at p may be, of those taken in
# the build of the names bs
def Imports.paths(
  xs: List<&2, Formats.Import>,
  +p: String,
  +bs: List<&2, List<&2, U32>>
) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{Formats.Import{Formats.Edge{t, al, ns, cs}, br, fi}, +rest}:
      Shared.Bool.when(
        List<&2, String>,
        Conds.taken(cs, bs),
        u => Names.paths(
          Resources.Name.candidates(
            Resources.Name{String.append(":", p)},
            fi,
            Texts.Bytes.to_text(t)
          ),
          Imports.paths(rest, p, bs)
        ),
        u => Imports.paths(rest, p, bs)
      )

# the paths that the resource at p, of the words ws, imports in the build of
# the conditions bs
def Format.imports(p: String, ws: List<&2, U32>, bs: List<&2, String>) -> List<&2, String>:
  +p = p
  Imports.paths(Formats.Format.uses(Formats.Format.guess(p), [ws]), p, Names.words(bs))

# Examples
# --------

# a C resource that includes one header in each part of a condition
def Example.c() -> List<&2, U32>:
  Texts.Bytes.of_text(
    "#include \"a.h\"\n#ifdef FOO\n#include \"b.h\"\n#else\n#include \"../c.h\"\n#endif\nint f() {\n  return 1;\n}\n\nint g() {\n  return 2;\n}\n"
  )

# its imports in the build that defines FOO
def Example.imports_foo() -> {
  Format.imports("src/x.c", Example.c(), ["FOO"]) == ["src/a.h", "src/b.h"]: List<&2, String>
}:
  {==}

# its imports in the build that defines nothing
def Example.imports_none() -> {
  Format.imports("src/x.c", Example.c(), []) == ["src/a.h", "c.h"]: List<&2, String>
}:
  {==}

# its items: each line of its head that starts at the margin, then each function
def Example.items() -> {
  List.length(&2, List<&2, U32>, Format.items("src/x.c", Example.c())) == 8n: Nat
}:
  {==}

# two changes of two functions merge
def Example.merge() -> {
  Format.merge(
    "x.c",
    Some{Texts.Bytes.of_text("a\nb\nc\nd\ne\n")},
    Some{Texts.Bytes.of_text("A\nb\nc\nd\ne\n")},
    Some{Texts.Bytes.of_text("a\nb\nc\nd\nE\n")}
  )
    == Some{Some{Texts.Bytes.of_text("A\nb\nc\nd\nE\n")}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  {==}

# two different changes of one line clash
def Example.clash() -> {
  Format.merge(
    "x.txt",
    Some{Texts.Bytes.of_text("a\n")},
    Some{Texts.Bytes.of_text("b\n")},
    Some{Texts.Bytes.of_text("c\n")}
  )
    == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  {==}

# the diff of a change of one line keeps the lines around it
def Example.diff() -> {
  Format.diff(
    "x.txt",
    Texts.Bytes.of_text("a\nb\nc\n"),
    Texts.Bytes.of_text("a\nB\nc\n")
  )
    == [Formats.Hunk{1n, 1n, [[66, 10]]}]: Diff()
}:
  {==}

# a diff does not apply to a content that is too short for it
def Example.apply_none() -> {
  Format.apply(
    "x.txt",
    [97, 10],
    [Formats.Hunk{1n, 1n, [[66, 10]]}]
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
  {==}

# the items of a Markdown resource: its lines, the markers of its code, and
# the lines of the code
def Example.nested() -> {
  Format.items(
    "a.md",
    Texts.Bytes.of_text("t\n```x\ny\n```z")
  )
    == [[116, 10], [96, 96, 96], [120, 10], [121, 10], [96, 96, 96], [122]]: List<&2, List<&2, U32>>
}:
  {==}
