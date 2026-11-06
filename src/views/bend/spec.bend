import Base
import ../../conditions/spec.bend as Cond
import ../../graph/spec.bend as Graph
import ../../shared.bend as Shared
import ../shared.bend as Views
import ../text/spec.bend as Text

# Bend: a resource whose bytes are UTF-8 Bend source. Its document is the
# list of its top-level items, split from the Text lines by one rule. Any
# text is a document, also one that does not parse or check: a file being
# edited is still versioned. The items are what the graph selects.

# The kinds of top-level item.
type ItemKind is Data:
  ImportItem{}
  TypeItem{}
  DefItem{}
  LawItem{}

# A top-level item and its text, with its line ends: a keyed item (its
# comment lines right above it, its head line, its body), or a gap (blank
# lines and loose comments between items, and anything before the first
# head).
type Item is Data:
  Keyed{kind: ItemKind, name: String, text: String}
  Gap{text: String}

# A Bend document.
type Module is Data:
  Module{items: List<&2, Item>}

# Lines
# -----

# The role of a line in splitting. Head: it starts an item, at column 0.
# Note: a comment at column 0. Blank: only spaces and tabs. Body: anything
# else, such as an indented line.
type Role is Data:
  Head{kind: ItemKind, name: String}
  Note{}
  Blank{}
  Body{}

# the name in s, the text after a head's keyword: up to the first ' ', '(',
# '<', ':' or '{'
def Bend.name.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      +x = Char.to_u32(c)
      stop = Bool.or(
        Bool.or(
          Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 40)),
          Bool.or(U32.is_eq(x, 60), U32.is_eq(x, 58))
        ),
        U32.is_eq(x, 123)
      )
      Shared.Bool.when(String, stop, u => SNil{}, u => SCon{c, Bend.name.go(t)})

# s is only spaces and tabs
def Bend.is_blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      List.all.if(u => Bend.is_blank(t), Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9)))

# the head for keyword k and kind, when s starts with k, else role r
def Bend.head(+s: String, k: String, kind: ItemKind, r: Role) -> Role:
  +k = k
  Shared.Bool.when(
    Role,
    String.starts_with(s, k),
    u => Head{kind, Bend.name.go(String.drop(s, String.length(k)))},
    u => r
  )

# the role of the line s: a head for "import ", "type ", "def ", "law " or
# "@unsafe def " at column 0, the import's name being all its text; a note
# for '#' at column 0; blank; or body
def Bend.role(+s: String) -> Role:
  other = Shared.Bool.when(
    Role,
    Bend.is_blank(s),
    u => Blank{},
    u => Shared.Bool.when(Role, String.starts_with(s, "#"), v => Note{}, v => Body{})
  )
  imp = Shared.Bool.when(
    Role,
    String.starts_with(s, "import "),
    u => Head{ImportItem{}, String.trim_end(String.drop(s, 7n))},
    u => other
  )
  Bend.head(
    s,
    "type ",
    TypeItem{},
    Bend.head(
      s,
      "def ",
      DefItem{},
      Bend.head(s, "law ", LawItem{}, Bend.head(s, "@unsafe def ", DefItem{}, imp))
    )
  )

# Splitting
# ---------

# the text of lines, last first
def Bend.text(rev: List<&2, Text.Line>) -> String:
  Text.Text.join(List.reverse(&2, Text.Line, rev))

# r is a note
def Role.is_note(r: Role) -> Bool:
  match r:
    case Note{}:
      True{}
    case _:
      False{}

# the line l is a note
def Bend.is_note(l: Text.Line) -> Bool:
  match l:
    case Text.Line{t, e}:
      Role.is_note(Bend.role(t))

# the notes that end pend (its first ones, as pend is last first): the run
# of notes right above a head; a blank line ends the run
def Bend.notes.run(pend: List<&2, Text.Line>) -> List<&2, Text.Line>:
  match pend:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      Shared.Bool.when(
        List<&2, Text.Line>,
        Bend.is_note(l),
        u => l <> Bend.notes.run(t),
        u => Nil{}
      )

# pend without the notes that end it
def Bend.notes.before(pend: List<&2, Text.Line>) -> List<&2, Text.Line>:
  match pend:
    case Nil{}:
      Nil{}
    case Con{+l, +t}:
      Shared.Bool.when(
        List<&2, Text.Line>,
        Bend.is_note(l),
        u => Bend.notes.before(t),
        u => Con{l, t}
      )

# The item being built: none yet, or a keyed item with its lines so far,
# last first.
type Open is Data:
  NoOpen{}
  OpenItem{kind: ItemKind, name: String, lines: List<&2, Text.Line>}

# the item of cur, if one is open
def Open.close(cur: Open) -> List<&2, Item>:
  match cur:
    case NoOpen{}:
      []
    case OpenItem{k, n, ls}:
      [Keyed{k, n, Bend.text(ls)}]

# a gap of the lines, last first, unless their text is empty
def Bend.gap(ls: List<&2, Text.Line>) -> List<&2, Item>:
  +t = Bend.text(ls)
  Shared.Bool.when(List<&2, Item>, String.is_empty(t), u => [], u => [Gap{t}])

# the items after the line l with role r; k goes on with the open item and
# the pending lines
def Bend.split.at(
  r: Role,
  l: Text.Line,
  cur: Open,
  +pend: List<&2, Text.Line>,
  k: Open -> List<&2, Text.Line> -> List<&2, Item>
) -> List<&2, Item>:
  match r cur:
    case Head{kd, nm} c:
      done = List.append(&2, Item, Open.close(c), Bend.gap(Bend.notes.before(pend)))
      List.append(&2, Item, done, k(OpenItem{kd, nm, l <> Bend.notes.run(pend)}, []))
    case Body{} NoOpen{}:
      List.append(&2, Item, Bend.gap(l <> pend), k(NoOpen{}, []))
    case Body{} OpenItem{kd, nm, ls}:
      k(OpenItem{kd, nm, l <> List.append(&2, Text.Line, pend, ls)}, [])
    case _ c:
      k(c, l <> pend)

# the items of the lines: cur is the open item; pend holds the notes and
# blank lines since its last body line, last first. A head closes cur; the
# notes right above the head join the new item, and the rest of pend
# becomes a gap. A body line takes pend into cur. Body lines before the
# first head become gaps.
def Bend.split.go(
  lines: List<&2, Text.Line>,
  cur: Open,
  pend: List<&2, Text.Line>
) -> List<&2, Item>:
  match lines:
    case Nil{}:
      List.append(&2, Item, Open.close(cur), Bend.gap(pend))
    case Con{+l, t}:
      Bend.split.at(Bend.role(Text.Line.text(l)), l, cur, pend, c => p => Bend.split.go(t, c, p))

# the items of s
def Bend.split(s: String) -> List<&2, Item>:
  Bend.split.go(Text.Text.lines(s), NoOpen{}, [])

# the text of an item
def Item.text(i: Item) -> String:
  match i:
    case Keyed{k, n, t}:
      t
    case Gap{t}:
      t

# the texts of items, one after another
def Bend.join.go(items: List<&2, Item>) -> String:
  match items:
    case Nil{}:
      SNil{}
    case Con{i, t}:
      String.append(Item.text(i), Bend.join.go(t))

# the text of a document: its items one after another
def Bend.join(m: Module) -> String:
  match m:
    case Module{items}:
      Bend.join.go(items)

# a and b are the same kind
def ItemKind.is_eq(a: ItemKind, b: ItemKind) -> Bool:
  match a b:
    case ImportItem{} ImportItem{}:
      True{}
    case TypeItem{} TypeItem{}:
      True{}
    case DefItem{} DefItem{}:
      True{}
    case LawItem{} LawItem{}:
      True{}
    case _ _:
      False{}

# a and b are the same item
def Item.is_eq(a: Item, b: Item) -> Bool:
  match a b:
    case Keyed{k1, n1, t1} Keyed{k2, n2, t2}:
      Bool.and(ItemKind.is_eq(k1, k2), Bool.and(String.eq(n1, n2), String.eq(t1, t2)))
    case Gap{t1} Gap{t2}:
      String.eq(t1, t2)
    case _ _:
      False{}

# xs and ys are the same items in the same order
def Items.is_eq(xs: List<&2, Item>, ys: List<&2, Item>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Items.is_eq(xt, yt), Item.is_eq(x, y))
    case _ _:
      False{}

# the items of m
def Module.items(m: Module) -> List<&2, Item>:
  match m:
    case Module{items}:
      items

# a document that the splitter gives for its own text: so no two documents
# have one text
def Bend.ok(m: Module) -> Bool:
  +m = m
  Items.is_eq(Bend.split(Bend.join(m)), Module.items(m))

# the document of UTF-8 bytes b, or None when b is not UTF-8
law Bend.decode:
  for b: Shared.Bytes()
  Maybe<&2, Module>

# the UTF-8 bytes of a document
def Bend.encode(m: Module) -> Shared.Bytes():
  Text.Text.encode(Bend.join(m))

# Bend loses nothing
law Bend.lossless:
  Views.View.Lossless(~Module, ~Bend.ok, ~Bend.decode, ~Bend.encode)

# Items and keys
# --------------

# the constructor names of a type item: each line of its text that is two
# spaces then a name
def Bend.ctors.go(ls: List<&2, Text.Line>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, +t}:
      +x = Text.Line.text(l)
      +rest = String.drop(x, 2n)
      ok = List.all.if(
        u => Bool.not(Bend.is_blank(String.take(rest, 1n))),
        String.starts_with(x, "  ")
      )
      Shared.Bool.when(
        List<&2, String>,
        ok,
        u => Bend.name.go(rest) <> Bend.ctors.go(t),
        u => Bend.ctors.go(t)
      )

# the names that item i defines: its name, and a type's constructors
def Item.names(i: Item) -> List<&2, String>:
  match i:
    case Keyed{TypeItem{}, n, t}:
      n <> Bend.ctors.go(Text.Text.lines(t))
    case Keyed{k, n, t}:
      [n]
    case Gap{t}:
      []

# the names of items, in order
def Items.names(items: List<&2, Item>) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      List.append(&2, String, Item.names(i), Items.names(t))

# how often n occurs in ns
def Keys.count(ns: List<&2, String>, +n: String) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{x, +t}:
      Shared.Bool.when(Nat, String.eq(x, n), u => 1n+Keys.count(t, n), u => Keys.count(t, n))

# the keys of names: a name that occurred before gets "#" and its count, so
# a file with a name defined twice (an edit in progress) still has
# distinct keys
def Keys.of.go(ns: List<&2, String>, seen: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      +seen = seen
      +c = Keys.count(seen, n)
      k = Shared.Bool.when(
        String,
        Nat.is_eq(c, 0n),
        u => n,
        u => String.append(n, String.append("#", Nat.show(1n+c)))
      )
      k <> Keys.of.go(t, n <> seen)

# the keys of a document: the names its items define, made distinct
def Bend.keys(m: Module) -> List<&2, String>:
  Keys.of.go(Items.names(Module.items(m)), [])

# every key names one item
law Bend.keys_distinct:
  Views.View.KeysDistinct(~Module, ~Bend.keys)

# the text of the item that defines key k in items, or None
def Bend.owner(items: List<&2, Item>, +k: String, seen: List<&2, String>) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{+i, t}:
      +seen = seen
      mine = Keys.of.go(Item.names(i), seen)
      Shared.Bool.when(
        Maybe<&2, String>,
        List.contains(~String, ~String.eq, mine, k),
        u => Some{Item.text(i)},
        u => Bend.owner(t, k, List.append(&2, String, Item.names(i), seen))
      )

# a and b are the same text, or both none
def Texts.opt_eq(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      String.eq(x, y)
    case _ _:
      False{}

# the keys of ks whose item differs between a and b: changed, added or gone
def Bend.changed.go(ks: List<&2, String>, +a: Module, +b: Module) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, +t}:
      same = Texts.opt_eq(Bend.owner(Module.items(a), k, []), Bend.owner(Module.items(b), k, []))
      Shared.Bool.when(
        List<&2, String>,
        same,
        u => Bend.changed.go(t, a, b),
        u => k <> Bend.changed.go(t, a, b)
      )

# what changed from a to b, for the graph: the keys whose item text differs
def Bend.changed(+a: Module, +b: Module) -> Graph.Change:
  Graph.Keys{Bend.changed.go(List.append(&2, String, Bend.keys(a), Bend.keys(b)), a, b)}

# Meaning
# -------

# the keyed items of items: gaps dropped
def Items.keyed(items: List<&2, Item>) -> List<&2, Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Keyed{k, n, x}, t}:
      Keyed{k, n, x} <> Items.keyed(t)
    case Con{Gap{x}, t}:
      Items.keyed(t)

# a and b mean the same: the same keyed items, text and order included
# (order matters in Bend: a def calls only defs above it); gaps are trivia
def Bend.same(a: Module, b: Module) -> Bool:
  Items.is_eq(Items.keyed(Module.items(a)), Items.keyed(Module.items(b)))

# Bend.same is an equivalence
law Bend.same_equivalence:
  Views.View.Equivalence(~Module, ~Bend.same)

# Diff and merge
# --------------

# One step of a diff: replace del items at pos with ins; each pos counts in
# the items as the steps before it left them.
type ItemEdit is Data:
  ItemEdit{pos: Nat, del: Nat, ins: List<&2, Item>}

# the steps that turn a into b, item by item
law Bend.diff:
  for a: Module
  for b: Module
  List<&2, ItemEdit>

# d after the steps, or None when a step does not fit
law Bend.patch:
  for d: Module
  for es: List<&2, ItemEdit>
  Maybe<&2, Module>

# no steps
def Edits.is_empty(es: List<&2, ItemEdit>) -> Bool:
  List.is_empty(&2, ItemEdit, es)

# the three-way merge of x and y from base, item by item. A key changed on
# one side only takes that side; a key changed the same way on both takes
# it; a key changed differently on both takes Text.merge of its three item
# texts, and is a clash (None) only when that clashes. Items that both
# sides insert at one place go in one order whichever side is which:
# callee before caller, else by key. Gaps follow the same rules as items.
law Bend.merge:
  for base: Module
  for x: Module
  for y: Module
  Maybe<&2, Module>

# a patch with a diff gives the target
law Bend.patches:
  Views.View.Patches(~Module, ~List<&2, ItemEdit>, ~Bend.diff, ~Bend.patch)

# a document has no diff to itself
law Bend.diffs_nothing:
  Views.View.DiffsNothing(~Module, ~List<&2, ItemEdit>, ~Bend.diff, ~Edits.is_empty)

# merge is a three-way merge
law Bend.merges:
  Views.View.Merges(~Module, ~Bend.merge)

# Imports
# -------
# An import with an alias selects only the names the module uses through
# it ("M.x"); one without an alias selects the whole target. A relative
# import names a file next to the importer; Base and hub packages are not
# resources of this store, so their edges stay unresolved.

# c may be part of a name: a letter, a digit, '_' or '.'
def Bend.is_ident(+c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(Bool.or(Char.is_alpha(c), Char.is_digit(c)), Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 46)))

# the name at the start of s
def Bend.ident.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Shared.Bool.when(String, Bend.is_ident(c), u => SCon{c, Bend.ident.go(t)}, u => SNil{})

# s without a '.' at its end
def Bend.trim_dot(+s: String) -> String:
  Shared.Bool.when(
    String,
    String.ends_with(s, "."),
    u => String.take(s, Nat.sub(String.length(s), 1n)),
    u => s
  )

# the names used through alias a in s: each "a." at the start of a name,
# and the name after it; start: s is at the start of a name
def Bend.uses.go(+s: String, +a: String, start: Bool) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{+c, t}:
      +rest = Bend.uses.go(t, a, Bool.not(Bend.is_ident(c)))
      +pre = String.append(a, ".")
      here = Bool.and(start, String.starts_with(s, pre))
      Shared.Bool.when(
        List<&2, String>,
        here,
        u => Bend.trim_dot(Bend.ident.go(String.drop(s, String.length(pre)))) <> rest,
        u => rest
      )

# the words of s, split at spaces
def Bend.words(s: String) -> List<&2, String>:
  String.split(s, ' ')

# the target of the import path p from n: relative paths resolve, others
# (Base, hub packages) stay unresolved
def Bend.target(n: Shared.Name, +p: String) -> Graph.Target:
  rel = Bool.or(String.starts_with(p, "./"), String.starts_with(p, "../"))
  Shared.Bool.when(Graph.Target, rel, u => Graph.Target.resolve(n, p), u => Graph.Unresolved{p})

# the edge of an import from n, given the words of its text and the text
# of the whole module: "path as Alias" selects what the module uses through
# Alias; anything else selects the whole target
def Bend.edge(+n: Shared.Name, ws: List<&2, String>, text: String) -> Graph.Edge:
  match ws:
    case Con{p, Con{a, Con{alias, Nil{}}}}:
      p = p
      sel = Shared.Bool.when(
        Graph.Selection,
        String.eq(a, "as"),
        u => Graph.Items{Bend.uses.go(text, alias, True{})},
        u => Graph.Whole{}
      )
      Graph.Edge{n, Bend.target(n, p), Graph.BendView{}, sel, Cond.Always{}}
    case Con{p, r}:
      Graph.Edge{n, Bend.target(n, p), Graph.BendView{}, Graph.Whole{}, Cond.Always{}}
    case Nil{}:
      Graph.Edge{n, Graph.Unresolved{""}, Graph.BendView{}, Graph.Whole{}, Cond.Always{}}

# the edges of the imports among items of a module from n with text text
def Bend.edges.go(items: List<&2, Item>, +n: Shared.Name, +text: String) -> List<&2, Graph.Edge>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Keyed{ImportItem{}, x, t}, r}:
      Bend.edge(n, Bend.words(x), text) <> Bend.edges.go(r, n, text)
    case Con{i, r}:
      Bend.edges.go(r, n, text)

# the edges of the document m of the resource n: one per import. Bend has
# no conditional imports, so every edge holds always.
def Bend.edges(n: Shared.Name, +m: Module) -> List<&2, Graph.Edge>:
  Bend.edges.go(Module.items(m), n, Bend.join(m))
