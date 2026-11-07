import Base
import ../conditions/spec.bend as Cond
import ../graph/impl.bend as GraphImpl
import ../graph/spec.bend as Graph
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../views/bend/impl.bend as BendImpl
import ../views/bend/spec.bend as Bend
import ../views/shared.bend as Vs
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text

# What the daemon asks of the views: a diff, a three-way merge, the edges
# a change affects, open obligations and a verifier. A resource whose path ends with ".bend" is read
# by the Bend view (by item), any other UTF-8 resource by the Text view (by
# line); other bytes have no view, so they only differ or not.

# the path ends with ".bend"
def View.is_bend(path: String) -> Bool:
  String.ends_with(path, ".bend")

# the Bend document of a text
def View.module(s: String) -> Bend.Module:
  Bend.Module{Bend.Bend.split(s)}

# the names of the items, one after another
def View.names(items: List<&2, Bend.Item>) -> String:
  match items:
    case Nil{}:
      ""
    case Con{Bend.Keyed{k, n, t}, r}:
      String.concat([" ", n, View.names(r)])
    case Con{Bend.Gap{t}, r}:
      String.append(" (blank)", View.names(r))

# the lines of a Bend diff, one per step
def View.item_edits(es: List<&2, Bend.ItemEdit>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Bend.ItemEdit{p, d, ins}, r}:
      String.concat(
        ["at item ", Nat.show(p), ": -", Nat.show(d), " +", View.names(ins)]
      )
        <> View.item_edits(r)

# the new lines of a diff, each marked with '+'
def View.added(ls: List<&2, Text.Line>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      String.append("+ ", Text.Line.text(l)) <> View.added(t)

# the lines of a Text diff: each step, then its new lines
def View.line_edits(es: List<&2, Text.LineEdit>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Text.LineEdit{p, d, +ins}, r}:
      List.append(
        &2,
        String,
        String.concat(
          [
            "at line ",
            Nat.show(p),
            ": -",
            Nat.show(d),
            " +",
            Nat.show(List.length(&2, Text.Line, ins))
          ]
        )
          <> View.added(ins),
        View.line_edits(r)
      )

# the diff of the texts x and y of the resource at path, by its view
def View.diff.texts(path: String, +x: String, +y: String) -> List<&2, String>:
  Bools.Bool.when(
    List<&2, String>,
    View.is_bend(path),
    u => View.item_edits(Bend.Bend.diff(View.module(x), View.module(y))),
    u => View.line_edits(Text.Text.diff(x, y))
  )

# the diff of two contents, given their texts when both are UTF-8
def View.diff.of(
  path: String,
  tx: Maybe<&2, String>,
  ty: Maybe<&2, String>,
  same: Bool
) -> List<&2, String>:
  match tx ty:
    case Some{x} Some{y}:
      View.diff.texts(path, x, y)
    case _ _:
      Bools.Bool.when(
        List<&2, String>,
        same,
        u => ["binary: the same"],
        u => ["binary: they differ"]
      )

# the lines of the diff from x to y of the resource at path
def View.diff(path: String, +x: Octets.Bytes(), +y: Octets.Bytes()) -> List<&2, String>:
  View.diff.of(path, Text.Text.decode(x), Text.Text.decode(y), Octets.Bytes.is_eq(x, y))

# the bytes of a merged text, if the merge did not clash
def View.merged.text(m: Maybe<&2, String>) -> Maybe<&2, Octets.Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{Text.Text.encode(s)}

# the bytes of a merged document, if the merge did not clash
def View.merged.module(m: Maybe<&2, Bend.Module>) -> Maybe<&2, Octets.Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Bend.Bend.encode(d)}

# the three-way merge of the texts, by the view of path
def View.merge.texts(path: String, +b: String, +x: String, +y: String) -> Maybe<&2, Octets.Bytes()>:
  Bools.Bool.when(
    Maybe<&2, Octets.Bytes()>,
    View.is_bend(path),
    u => View.merged.module(Bend.Bend.merge(View.module(b), View.module(x), View.module(y))),
    u => View.merged.text(Text.Text.merge(b, x, y))
  )

# the merge of three contents, given their texts when all are UTF-8; bytes
# with no view clash, as the caller took the cases where a side is the base
def View.merge.of(
  path: String,
  tb: Maybe<&2, String>,
  tx: Maybe<&2, String>,
  ty: Maybe<&2, String>
) -> Maybe<&2, Octets.Bytes()>:
  match tb tx ty:
    case Some{b} Some{x} Some{y}:
      View.merge.texts(path, b, x, y)
    case _ _ _:
      None{}

# the three-way merge of x and y from b, of the resource at path, or None
# for a clash
def View.merge(
  path: String,
  b: Octets.Bytes(),
  x: Octets.Bytes(),
  y: Octets.Bytes()
) -> Maybe<&2, Octets.Bytes()>:
  View.merge.of(path, Text.Text.decode(b), Text.Text.decode(x), Text.Text.decode(y))

# the edges among es that a change c of the resource n affects, under any
# configuration
def View.affected(
  es: List<&2, Graph.Edge>,
  n: Resources.Name,
  c: Graph.Change
) -> List<&2, Graph.Edge>:
  Graph.Graph.affected(Graph.Graph{es}, n, c, Cond.Always{})

# the Bend document of the resource n with the text found
def View.doc.of(n: Resources.Name, m: Maybe<&2, String>) -> List<&2, Bend.Doc>:
  match m:
    case None{}:
      []
    case Some{s}:
      [Bend.Doc{n, View.module(s)}]

# the Bend document of the resource n at path with the bytes b, when it is
# a Bend resource whose bytes are UTF-8
def View.doc(n: Resources.Name, path: String, b: Octets.Bytes()) -> List<&2, Bend.Doc>:
  View.doc.of(
    n,
    Bools.Bool.when(Maybe<&2, String>, View.is_bend(path), u => Text.Text.decode(b), u => None{})
  )

# the open obligations of the one document found, given ds
def View.obligations.of(
  ds: List<&2, Bend.Doc>,
  found: List<&2, Bend.Doc>
) -> List<&2, Vs.Obligation>:
  match found:
    case Con{d, Nil{}}:
      Bend.Bend.obligations(ds, d)
    case _:
      []

# the open obligations of the resource n at path with the bytes b, given ds,
# the line's Bend documents: the Bend view's; no other view has any yet
def View.obligations(
  ds: List<&2, Bend.Doc>,
  n: Resources.Name,
  path: String,
  b: Octets.Bytes()
) -> List<&2, Vs.Obligation>:
  View.obligations.of(ds, View.doc(n, path, b))

# the verifier of the resource at path: the Bend view's; no other view has
# one yet
def View.verifier(path: String) -> Maybe<&2, Vs.Verifier>:
  Bools.Bool.when(
    Maybe<&2, Vs.Verifier>,
    View.is_bend(path),
    u => Some{Bend.Bend.verifier()},
    u => None{}
  )
