import Base
import ../conditions/spec.bend as Cond
import ../graph/spec.bend as Graph
import ../lines/spec.bend as Lines
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../views/bend/spec.bend as Bend

# Impact: what a change of Bend source means, and how far it reaches.
#
# The guarantee this serves: when no law statement changed and the merged
# result passes the checker, every law still holds. Bend is sound, so a
# proof that checks is a proof; the classes below tell whether a change
# touched a statement (a person reviews it), only proofs (nothing a law
# promises can change), or code that laws observe or do not observe.

# Classification
# --------------

# What a change to one key of a module is. ProofOnly: a def that fills a
# law whose statement did not change. LawStatement: a law item's text, or
# the proof of a law of this module whose statement changed with it.
# Covered: other code that some law statement observes (Impact.covered).
# Uncovered: any other change. Added, Removed: the key is new, or gone.
type Class is Data:
  ProofOnly{}
  LawStatement{}
  Covered{}
  Uncovered{}
  Added{}
  Removed{}

# the text of the law item named x among items, or None
def Impact.statement(items: List<&2, Bend.Item>, +x: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{Bend.Keyed{Bend.LawItem{}, y, t}, r}:
      Bools.Bool.when(Maybe<&2, String>, String.eq(y, x), u => Some{t}, u => Impact.statement(r, x))
    case Con{i, r}:
      Impact.statement(r, x)

# the local names among mentions
def Mentions.locals(ms: List<&2, Bend.Mention>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Bend.Local{x}, t}:
      x <> Mentions.locals(t)
    case Con{Bend.Imported{g, x}, t}:
      Mentions.locals(t)

# p is a statement
def Impact.is_statement(p: Bend.Part) -> Bool:
  match p:
    case Bend.Statement{}:
      True{}
    case _:
      False{}

# p is code
def Impact.is_code(p: Bend.Part) -> Bool:
  match p:
    case Bend.Code{}:
      True{}
    case _:
      False{}

# the local mentions of every law item among items of m
def Impact.observed(
  items: List<&2, Bend.Item>,
  +n: Resources.Name,
  +m: Bend.Module
) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{+i, r}:
      +rest = Impact.observed(r, n, m)
      Bools.Bool.when(
        List<&2, String>,
        Impact.is_statement(Bend.Bend.part(m, n, i)),
        u => List.append(&2, String, Mentions.locals(Bend.Bend.refs(n, m, i)), rest),
        u => rest
      )

# Impact.code_mentions of the item found, if any
def Impact.code_mentions.of(
  +n: Resources.Name,
  +m: Bend.Module,
  o: Maybe<&2, Bend.Item>
) -> List<&2, String>:
  match o:
    case None{}:
      []
    case Some{+i}:
      Bools.Bool.when(
        List<&2, String>,
        Impact.is_code(Bend.Bend.part(m, n, i)),
        u => Mentions.locals(Bend.Bend.refs(n, m, i)),
        u => []
      )

# the names that the item named x mentions, when it is code; none for a
# proof or a statement, or when no item is named x
def Impact.code_mentions(n: Resources.Name, +m: Bend.Module, x: String) -> List<&2, String>:
  Impact.code_mentions.of(n, m, Bend.Bend.owner_item(Bend.Module.items(m), x, []))

# ns with every name of xs that ns lacks
def Names.add(xs: List<&2, String>, +ns: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      ns
    case Con{+x, +t}:
      Bools.Bool.when(
        List<&2, String>,
        List.contains(~String, ~String.eq, ns, x),
        u => Names.add(t, ns),
        u => Names.add(t, x <> ns)
      )

# the names of xs that seen lacks
def Impact.unseen(xs: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Bools.Bool.when(
        List<&2, String>,
        List.contains(~String, ~String.eq, seen, x),
        u => Impact.unseen(t, seen),
        u => x <> Impact.unseen(t, seen)
      )

# the closure of seen under code mentions, from the frontier todo; fuel
# counts the names left to visit
def Impact.covered.go(
  fuel: Nat,
  +n: Resources.Name,
  +m: Bend.Module,
  todo: List<&2, String>,
  +seen: List<&2, String>
) -> List<&2, String>:
  match fuel todo:
    case 0n t:
      seen
    case 1n+f Nil{}:
      seen
    case 1n+f Con{x, t}:
      new = Impact.code_mentions(n, m, x)
      +fresh = Names.add(new, [])
      grown = Names.add(fresh, seen)
      Impact.covered.go(f, n, m, List.append(&2, String, t, Impact.unseen(fresh, seen)), grown)

# The names that law statements observe in the module m of the resource n:
# every name a law item mentions, then every name the code items reached
# so far mention, and so on. Proofs are not followed: a proof uses names to
# show a law, it does not constrain them.
def Impact.covered(+n: Resources.Name, +m: Bend.Module) -> List<&2, String>:
  +start = Names.add(Impact.observed(Bend.Module.items(m), n, m), [])
  fuel = {1n+List.length(&2, String, Bend.Items.names(Bend.Module.items(m))): Nat}
  Impact.covered.go(fuel, n, m, start, start)

# some name of xs is in ys
def Names.meet(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      List.any.if(u => Names.meet(t, ys), List.contains(~String, ~String.eq, ys, x))

# x is a law of new, and its statement in new differs from the one in base
def Impact.moved(+x: String, base: Bend.Module, new: Bend.Module) -> Bool:
  +c = Impact.statement(Bend.Module.items(new), x)
  List.all.if(
    u => Bool.not(Bend.Texts.opt_eq(Impact.statement(Bend.Module.items(base), x), c)),
    Maybe.is_some(&2, String, c)
  )

# the class of a change to an item of new whose part is p and whose names
# are names, when its text changed: a statement, a proof of a law of new
# whose statement changed too, a proof, or code observed or not
def Impact.class.of(
  p: Bend.Part,
  names: List<&2, String>,
  n: Resources.Name,
  base: Bend.Module,
  new: Bend.Module
) -> Class:
  match p:
    case Bend.Statement{}:
      LawStatement{}
    case Bend.Proof{x}:
      Bools.Bool.when(Class, Impact.moved(x, base, new), u => LawStatement{}, u => ProofOnly{})
    case Bend.Code{}:
      cov = Impact.covered(n, new)
      Bools.Bool.when(Class, Names.meet(names, cov), u => Covered{}, u => Uncovered{})

# the class of a change from the item ob of base to the item on of new, by
# one key: None when both are the same text or both are missing
def Impact.classify.of(
  +n: Resources.Name,
  base: Bend.Module,
  +new: Bend.Module,
  ob: Maybe<&2, Bend.Item>,
  on: Maybe<&2, Bend.Item>
) -> Maybe<&2, Class>:
  match ob on:
    case None{} None{}:
      None{}
    case None{} Some{b}:
      Some{Added{}}
    case Some{a} None{}:
      Some{Removed{}}
    case Some{a} Some{+b}:
      Bools.Bool.when(
        Maybe<&2, Class>,
        String.eq(Bend.Item.text(a), Bend.Item.text(b)),
        u => None{},
        u => Some{Impact.class.of(Bend.Bend.part(new, n, b), Bend.Item.names(b), n, base, new)}
      )

# the class of the change of key k from base to new in the resource n, or
# None when its item did not change
def Impact.classify(
  n: Resources.Name,
  +base: Bend.Module,
  +new: Bend.Module,
  +k: String
) -> Maybe<&2, Class>:
  ob = Bend.Bend.owner_item(Bend.Module.items(base), k, [])
  Impact.classify.of(n, base, new, ob, Bend.Bend.owner_item(Bend.Module.items(new), k, []))

# A key and the class of its change.
type Classified is Data:
  Classified{key: String, class: Class}

# the classified key k, if it changed, before rest
def Impact.classes.at(
  k: String,
  c: Maybe<&2, Class>,
  rest: List<&2, Classified>
) -> List<&2, Classified>:
  match c:
    case None{}:
      rest
    case Some{x}:
      Classified{k, x} <> rest

# the classes of the keys ks that changed
def Impact.classes.go(
  ks: List<&2, String>,
  +n: Resources.Name,
  +base: Bend.Module,
  +new: Bend.Module
) -> List<&2, Classified>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, t}:
      rest = Impact.classes.go(t, n, base, new)
      Impact.classes.at(k, Impact.classify(n, base, new, k), rest)

# the classes of every key that changed from base to new in the resource n
def Impact.classes(
  n: Resources.Name,
  +base: Bend.Module,
  +new: Bend.Module
) -> List<&2, Classified>:
  ks = Names.add(List.append(&2, String, Bend.Bend.keys(base), Bend.Bend.keys(new)), [])
  Impact.classes.go(List.reverse(&2, String, ks), n, base, new)

# a and b are the same class
def Class.is_eq(a: Class, b: Class) -> Bool:
  match a b:
    case ProofOnly{} ProofOnly{}:
      True{}
    case LawStatement{} LawStatement{}:
      True{}
    case Covered{} Covered{}:
      True{}
    case Uncovered{} Uncovered{}:
      True{}
    case Added{} Added{}:
      True{}
    case Removed{} Removed{}:
      True{}
    case _ _:
      False{}

# the answer m is the class c
def Impact.is(m: Maybe<&2, Class>, c: Class) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Class.is_eq(x, c)

# the part p is a proof
def Impact.is_proof(p: Bend.Part) -> Bool:
  match p:
    case Bend.Proof{x}:
      True{}
    case _:
      False{}

# the part p fills a law whose statement changed from base to new
def Impact.fills_moved(p: Bend.Part, base: Bend.Module, new: Bend.Module) -> Bool:
  match p:
    case Bend.Proof{x}:
      Impact.moved(x, base, new)
    case _:
      False{}

# Laws of the classification
# --------------------------

# a key is unclassified exactly when its item text is the same, or missing,
# on both sides
law classify_unchanged:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  {
    Maybe.is_none(
      &2,
      Class,
      Impact.classify(n, base, new, k)
    )
      == Bend.Texts.opt_eq(
        Bend.Bend.owner(Bend.Module.items(base), k),
        Bend.Bend.owner(Bend.Module.items(new), k)
      ): Bool
  }

# Added exactly when only new has the key
law classify_added:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  {
    Impact.is(
      Impact.classify(n, base, new, k),
      Added{}
    )
      == Bool.and(
        Maybe.is_none(&2, String, Bend.Bend.owner(Bend.Module.items(base), k)),
        Maybe.is_some(&2, String, Bend.Bend.owner(Bend.Module.items(new), k))
      ): Bool
  }

# Removed exactly when only base has the key
law classify_removed:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  {
    Impact.is(
      Impact.classify(n, base, new, k),
      Removed{}
    )
      == Bool.and(
        Maybe.is_some(&2, String, Bend.Bend.owner(Bend.Module.items(base), k)),
        Maybe.is_none(&2, String, Bend.Bend.owner(Bend.Module.items(new), k))
      ): Bool
  }

# for a key whose item a in base and b in new differ: LawStatement exactly
# when b is a law item, or the proof of a law of new whose statement changed
law classify_statement:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  for a: Bend.Item
  for b: Bend.Item
  for ha: {Bend.Bend.owner_item(Bend.Module.items(base), k, []) == Some{a}: Maybe<&2, Bend.Item>}
  for hb: {Bend.Bend.owner_item(Bend.Module.items(new), k, []) == Some{b}: Maybe<&2, Bend.Item>}
  for d: {String.eq(Bend.Item.text(a), Bend.Item.text(b)) == False{}: Bool}
  {
    Impact.is(
      Impact.classify(n, base, new, k),
      LawStatement{}
    )
      == Bool.or(
        Impact.is_statement(Bend.Bend.part(new, n, b)),
        Impact.fills_moved(Bend.Bend.part(new, n, b), base, new)
      ): Bool
  }

# for such a key: ProofOnly exactly when b is a proof whose law statement
# did not change
law classify_proof_only:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  for a: Bend.Item
  for b: Bend.Item
  for ha: {Bend.Bend.owner_item(Bend.Module.items(base), k, []) == Some{a}: Maybe<&2, Bend.Item>}
  for hb: {Bend.Bend.owner_item(Bend.Module.items(new), k, []) == Some{b}: Maybe<&2, Bend.Item>}
  for d: {String.eq(Bend.Item.text(a), Bend.Item.text(b)) == False{}: Bool}
  {
    Impact.is(
      Impact.classify(n, base, new, k),
      ProofOnly{}
    )
      == Bool.and(
        Impact.is_proof(Bend.Bend.part(new, n, b)),
        Bool.not(Impact.fills_moved(Bend.Bend.part(new, n, b), base, new))
      ): Bool
  }

# for such a key: Covered exactly when b is code that a law statement of new
# observes
law classify_covered:
  for n: Resources.Name
  for base: Bend.Module
  for new: Bend.Module
  for k: String
  for a: Bend.Item
  for b: Bend.Item
  for ha: {Bend.Bend.owner_item(Bend.Module.items(base), k, []) == Some{a}: Maybe<&2, Bend.Item>}
  for hb: {Bend.Bend.owner_item(Bend.Module.items(new), k, []) == Some{b}: Maybe<&2, Bend.Item>}
  for d: {String.eq(Bend.Item.text(a), Bend.Item.text(b)) == False{}: Bool}
  {
    Impact.is(
      Impact.classify(n, base, new, k),
      Covered{}
    )
      == Bool.and(
        Impact.is_code(Bend.Bend.part(new, n, b)),
        Names.meet(Bend.Item.names(b), Impact.covered(n, new))
      ): Bool
  }

# Blast radius
# ------------
# How far a change reaches: every item that mentions a changed item, then
# every item that mentions those, and so on, inside a module and across
# modules through imports. A cross-module step goes through an import edge
# of the graph and carries its condition; conditions are reported, not used
# to prune, until Cond.sat is implemented.

# A Bend document of a resource.
type Doc is Data:
  Doc{name: Resources.Name, module: Bend.Module}

# the name of d
def Doc.name(d: Doc) -> Resources.Name:
  match d:
    case Doc{n, m}:
      n

# the module of d
def Doc.module(d: Doc) -> Bend.Module:
  match d:
    case Doc{n, m}:
      m

# An item of a resource, by name.
type Spot is Data:
  Spot{at: Resources.Name, name: String}

# a and b are the same spot
def Spot.is_eq(a: Spot, b: Spot) -> Bool:
  match a b:
    case Spot{m, x} Spot{n, y}:
      List.all.if(u => String.eq(x, y), String.eq(Resources.Name.show(m), Resources.Name.show(n)))

# the mention x, from an item of the resource at, names the spot s
def Impact.names(x: Bend.Mention, at: Resources.Name, s: Spot) -> Bool:
  match x s:
    case Bend.Local{a} Spot{n, b}:
      Bool.and(String.eq(Resources.Name.show(at), Resources.Name.show(n)), String.eq(a, b))
    case Bend.Imported{t, a} Spot{n, b}:
      Bool.and(Graph.Target.is_eq(t, Graph.Named{n}), String.eq(a, b))

# the mention ms holds, from an item of the resource at, names the spot s:
# a local mention when at is s's resource, an imported one whose target is
# s's resource otherwise
def Impact.mentions(ms: List<&2, Bend.Mention>, +at: Resources.Name, +s: Spot) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{x, t}:
      List.any.if(u => Impact.mentions(t, at, s), Impact.names(x, at, s))

# the spots of the keyed items among items of the document d that mention s
def Impact.users.items(items: List<&2, Bend.Item>, +d: Doc, +s: Spot) -> List<&2, Spot>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Bend.Keyed{k, +x, t}, r}:
      i = {Bend.Keyed{k, x, t}: Bend.Item}
      +rest = Impact.users.items(r, d, s)
      Bools.Bool.when(
        List<&2, Spot>,
        Impact.mentions(Bend.Bend.refs(Doc.name(d), Doc.module(d), i), Doc.name(d), s),
        u => Spot{Doc.name(d), x} <> rest,
        u => rest
      )
    case Con{Bend.Gap{t}, r}:
      Impact.users.items(r, d, s)

# the spots of every document of docs that mention s directly
def Impact.users(docs: List<&2, Doc>, +s: Spot) -> List<&2, Spot>:
  match docs:
    case Nil{}:
      Nil{}
    case Con{+d, r}:
      List.append(
        &2,
        Spot,
        Impact.users.items(Bend.Module.items(Doc.module(d)), d, s),
        Impact.users(r, s)
      )

# xs without the spots of seen
def Spots.unseen(xs: List<&2, Spot>, +seen: List<&2, Spot>) -> List<&2, Spot>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Bools.Bool.when(
        List<&2, Spot>,
        List.contains(~Spot, ~Spot.is_eq, seen, x),
        u => Spots.unseen(t, seen),
        u => x <> Spots.unseen(t, x <> seen)
      )

# the closure of seen under users, from the frontier todo; fuel bounds the
# spots to visit
def Impact.radius.go(
  fuel: Nat,
  +docs: List<&2, Doc>,
  todo: List<&2, Spot>,
  +seen: List<&2, Spot>
) -> List<&2, Spot>:
  match fuel todo:
    case 0n t:
      seen
    case 1n+f Nil{}:
      seen
    case 1n+f Con{s, t}:
      +fresh = Spots.unseen(Impact.users(docs, s), seen)
      Impact.radius.go(f, docs, List.append(&2, Spot, fresh, t), List.append(&2, Spot, fresh, seen))

# the number of keyed items of docs
def Docs.size(docs: List<&2, Doc>) -> Nat:
  match docs:
    case Nil{}:
      0n
    case Con{d, r}:
      Nat.add(
        List.length(&2, Bend.Item, Bend.Items.keyed(Bend.Module.items(Doc.module(d)))),
        Docs.size(r)
      )

# The blast radius of the changed spots in docs: the changed spots, and every
# spot that mentions a spot of the radius. Each spot is visited once, so the
# fuel (the spots of docs and the changed ones) always suffices.
def Impact.radius(+docs: List<&2, Doc>, +changed: List<&2, Spot>) -> List<&2, Spot>:
  +start = Spots.unseen(changed, [])
  fuel = {1n+Nat.add(Docs.size(docs), List.length(&2, Spot, changed)): Nat}
  Impact.radius.go(fuel, docs, start, start)

# the rest r of a path after prev is a chain of direct uses that ends at s
def Path.ok.go(r: List<&2, Spot>, +docs: List<&2, Doc>, prev: Spot, s: Spot) -> Bool:
  match r:
    case Nil{}:
      Spot.is_eq(prev, s)
    case Con{+q, t}:
      List.all.if(
        u => Path.ok.go(t, docs, q, s),
        List.contains(~Spot, ~Spot.is_eq, Impact.users(docs, prev), q)
      )

# path is a chain of direct uses that starts at a changed spot and ends at s:
# its first spot is changed, each next spot mentions the one before it
def Path.ok(docs: List<&2, Doc>, changed: List<&2, Spot>, path: List<&2, Spot>, s: Spot) -> Bool:
  match path:
    case Nil{}:
      False{}
    case Con{+p, r}:
      List.all.if(u => Path.ok.go(r, docs, p, s), List.contains(~Spot, ~Spot.is_eq, changed, p))

# every changed spot is in the radius
law radius_has_changed:
  for docs: List<&2, Doc>
  for changed: List<&2, Spot>
  for s: Spot
  for h: {List.contains(~Spot, ~Spot.is_eq, changed, s) == True{}: Bool}
  {List.contains(~Spot, ~Spot.is_eq, Impact.radius(docs, changed), s) == True{}: Bool}

# the radius is closed: a spot that mentions a spot of the radius is in it
law radius_closed:
  for docs: List<&2, Doc>
  for changed: List<&2, Spot>
  for s: Spot
  for u: Spot
  for h: {List.contains(~Spot, ~Spot.is_eq, Impact.radius(docs, changed), s) == True{}: Bool}
  for k: {List.contains(~Spot, ~Spot.is_eq, Impact.users(docs, s), u) == True{}: Bool}
  {List.contains(~Spot, ~Spot.is_eq, Impact.radius(docs, changed), u) == True{}: Bool}

# the radius is minimal: each of its spots reaches a changed spot through a
# chain of direct uses
law radius_minimal:
  for docs: List<&2, Doc>
  for changed: List<&2, Spot>
  for s: Spot
  for h: {List.contains(~Spot, ~Spot.is_eq, Impact.radius(docs, changed), s) == True{}: Bool}
  exs path: List<&2, Spot>
  {Path.ok(docs, changed, path, s) == True{}: Bool}

# Layers
# ------

# An import edge that the radius crosses: from the importer to the target,
# with the condition under which the edge holds.
type Via is Data:
  Via{from: Resources.Name, to: Resources.Name, cond: Cond.Cond}

# The radius in layers. statements: the law items it holds; proofs: the
# proofs it holds; code: the rest. resources: every resource with a spot in
# it. lines: the lines that follow one of those resources (their heads for
# it are not empty). via: the import edges between its resources.
type Layers is Data:
  Layers{
    statements: List<&2, Spot>,
    proofs: List<&2, Spot>,
    code: List<&2, Spot>,
    resources: List<&2, Resources.Name>,
    lines: List<&2, String>,
    via: List<&2, Via>
  }

# the document of the resource n in docs, if any
def Docs.find(docs: List<&2, Doc>, +n: Resources.Name) -> Maybe<&2, Doc>:
  match docs:
    case Nil{}:
      None{}
    case Con{+d, r}:
      Bools.Bool.when(
        Maybe<&2, Doc>,
        String.eq(Resources.Name.show(Doc.name(d)), Resources.Name.show(n)),
        u => Some{d},
        u => Docs.find(r, n)
      )

# the part of the item found in m of the resource n; Code when none is
def Impact.part.item(m: Bend.Module, n: Resources.Name, o: Maybe<&2, Bend.Item>) -> Bend.Part:
  match o:
    case None{}:
      Bend.Code{}
    case Some{i}:
      Bend.Bend.part(m, n, i)

# the part of the item named x in the document d; Code when there is none
def Impact.part.in(d: Maybe<&2, Doc>, x: String) -> Bend.Part:
  match d:
    case None{}:
      Bend.Code{}
    case Some{+doc}:
      +m = Doc.module(doc)
      Impact.part.item(m, Doc.name(doc), Bend.Bend.owner_item(Bend.Module.items(m), x, []))

# the part that the spot s plays in docs; Code when its item is not there
def Impact.part.at(docs: List<&2, Doc>, s: Spot) -> Bend.Part:
  match s:
    case Spot{n, x}:
      Impact.part.in(Docs.find(docs, n), x)

# A layer of the radius: statements, proofs, or the rest.
type Layer is Data:
  OfStatements{}
  OfProofs{}
  OfCode{}

# the part p belongs to the layer l
def Layer.has(l: Layer, p: Bend.Part) -> Bool:
  match l p:
    case OfStatements{} Bend.Statement{}:
      True{}
    case OfProofs{} Bend.Proof{x}:
      True{}
    case OfCode{} Bend.Code{}:
      True{}
    case _ _:
      False{}

# the spots of ss in the layer l
def Impact.layer(ss: List<&2, Spot>, +docs: List<&2, Doc>, +l: Layer) -> List<&2, Spot>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      +rest = Impact.layer(t, docs, l)
      Bools.Bool.when(
        List<&2, Spot>,
        Layer.has(l, Impact.part.at(docs, s)),
        u => s <> rest,
        u => rest
      )

# ns holds the resource n
def Names.has(ns: List<&2, Resources.Name>, +n: Resources.Name) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{m, t}:
      List.any.if(u => Names.has(t, n), String.eq(Resources.Name.show(m), Resources.Name.show(n)))

# the resources of ss, each once
def Impact.resources(
  ss: List<&2, Spot>,
  seen: List<&2, Resources.Name>
) -> List<&2, Resources.Name>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Spot{+n, x}, +t}:
      +seen = seen
      Bools.Bool.when(
        List<&2, Resources.Name>,
        Names.has(seen, n),
        u => Impact.resources(t, seen),
        u => n <> Impact.resources(t, n <> seen)
      )

# the line l follows one of the resources rs: its heads for it are not empty
def Impact.follows(+l: Lines.Line, rs: List<&2, Resources.Name>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, t}:
      List.any.if(
        u => Impact.follows(l, t),
        Bool.not(List.is_empty(&2, Octets.Bytes(), Lines.Line.heads(l, r)))
      )

# the names of the lines of ls that follow one of the resources rs
def Impact.lines(ls: List<&2, Lines.Line>, +rs: List<&2, Resources.Name>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      +rest = Impact.lines(t, rs)
      Bools.Bool.when(
        List<&2, String>,
        Impact.follows(l, rs),
        u => Lines.Line.name(l) <> rest,
        u => rest
      )

# the import edges es of a resource that point at one of the resources rs
def Impact.via.edges(es: List<&2, Graph.Edge>, +rs: List<&2, Resources.Name>) -> List<&2, Via>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Graph.Edge{f, Graph.Named{n}, v, s, c}, t}:
      +n = n
      +rest = Impact.via.edges(t, rs)
      Bools.Bool.when(List<&2, Via>, Names.has(rs, n), u => Via{f, n, c} <> rest, u => rest)
    case Con{e, t}:
      Impact.via.edges(t, rs)

# the import edges between the resources rs, from their documents in docs
def Impact.via(docs: List<&2, Doc>, +rs: List<&2, Resources.Name>) -> List<&2, Via>:
  match docs:
    case Nil{}:
      Nil{}
    case Con{Doc{n, m}, t}:
      +n = n
      +rest = Impact.via(t, rs)
      Bools.Bool.when(
        List<&2, Via>,
        Names.has(rs, n),
        u => List.append(&2, Via, Impact.via.edges(Bend.Bend.edges(n, m), rs), rest),
        u => rest
      )

# the spot s is in the statements, proofs or code of y
def Impact.in_layers(y: Layers, +s: Spot) -> Bool:
  match y:
    case Layers{a, b, c, d, e, f}:
      Bool.or(
        List.contains(~Spot, ~Spot.is_eq, a, s),
        Bool.or(List.contains(~Spot, ~Spot.is_eq, b, s), List.contains(~Spot, ~Spot.is_eq, c, s))
      )

# the blast radius of the changed spots in docs, in layers, with the lines
# of ls that follow its resources
def Impact.layers(
  +docs: List<&2, Doc>,
  ls: List<&2, Lines.Line>,
  changed: List<&2, Spot>
) -> Layers:
  +r = Impact.radius(docs, changed)
  +rs = Impact.resources(r, [])
  Layers{
    Impact.layer(r, docs, OfStatements{}),
    Impact.layer(r, docs, OfProofs{}),
    Impact.layer(r, docs, OfCode{}),
    rs,
    Impact.lines(ls, rs),
    Impact.via(docs, rs)
  }

# the three layers hold exactly the spots of the radius
law layers_cover:
  for docs: List<&2, Doc>
  for ls: List<&2, Lines.Line>
  for changed: List<&2, Spot>
  for s: Spot
  {
    List.contains(
      ~Spot,
      ~Spot.is_eq,
      Impact.radius(docs, changed),
      s
    )
      == Impact.in_layers(Impact.layers(docs, ls, changed), s): Bool
  }
