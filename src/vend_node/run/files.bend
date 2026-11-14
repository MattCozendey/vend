import Base
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared

# Files
# -----
# The content of a version: a map from paths to words. It is a plain crit-bit
# map under the code of the path, so two versions share every part that did
# not change, and no proof is built when it changes. An entry holds its path
# beside its words, and it counts only when its key is the code of that path.
# The laws are in shared/files.bend: they hold of a map that is well formed
# (Files.wf), as each map made here from Files.new by Files.set is.

# a file: its path and its words
type Files.Item is Data:
  Files.Item{path: String, words: List<&2, U32>}

# the content of a version: the files, each under the code of its path
type Files is Data:
  Files{crit: Crits.Crit<Files.Item>}

# the key of the path p: its code
def Files.key(p: String) -> List<&2, U32>:
  Codes.Code.text(p, [])

# the words of the file m, when its path is p
def Files.get.of(m: Maybe<&2, Files.Item>, p: String) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{Files.Item{q, ws}}:
      Bool.pick(Maybe<&2, List<&2, U32>>, String.eq(q, p), Some{ws}, None{})

# the words at the path p in t
def Files.get(t: Files, +p: String) -> Maybe<&2, List<&2, U32>>:
  match t:
    case Files{d}:
      Files.get.of(Crits.Crit.get(Files.Item, d, Files.key(p)), p)

# no file
def Files.new() -> Files:
  Files{Crits.Crit.new(Files.Item)}

# t with the words w at the path p: none deletes the path
def Files.set(t: Files, +p: String, w: Maybe<&2, List<&2, U32>>) -> Files:
  match t w:
    case Files{d} None{}:
      Files{Crits.Crit.drop(Files.Item, d, Files.key(p))}
    case Files{d} Some{ws}:
      Files{Crits.Crit.set(~Files.Item, d, Files.key(p), Files.Item{p, ws})}

# rest, after the path q when hit
def Files.paths.if(hit: Bool, q: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      q <> rest
    case False{}:
      rest

# the paths of the entries es whose key is the code of their path
def Files.paths.go(es: List<&2, Crits.Bind<Files.Item>>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{k, Files.Item{+q, ws}}, r}:
      Files.paths.if(Crits.Key.is_eq(k, Files.key(q)), q, Files.paths.go(r))

# the paths that hold words in t, in the order of their codes
def Files.paths(t: Files) -> List<&2, String>:
  match t:
    case Files{d}:
      Files.paths.go(Crits.Crit.entries(Files.Item, d))

# the code of the files of the entries es, then r
def Files.code.go(es: List<&2, Crits.Bind<Files.Item>>, r: List<&2, U32>) -> List<&2, U32>:
  match es:
    case Nil{}:
      r
    case Con{Crits.Bind{k, Files.Item{q, ws}}, rest}:
      Codes.Code.text(q, Codes.Code.words(ws, Files.code.go(rest, r)))

# the code of t: each path that holds words, then its words
def Files.code(t: Files) -> List<&2, U32>:
  match t:
    case Files{d}:
      +es = Crits.Crit.entries(Files.Item, d)
      Codes.Code.count(List.length(&2, Crits.Bind<Files.Item>, es), Files.code.go(es, []))

# the hash of t: the SHA-256 of its code
def Files.hash(t: Files) -> Hashes.Hash:
  Hashes.Sha.hash(Files.code(t))

# the files a and b are the same: their paths and their words
def Files.Item.same(a: Files.Item, b: Files.Item) -> Bool:
  match a b:
    case Files.Item{p, ws} Files.Item{q, vs}:
      Bool.and(String.eq(p, q), Crits.Key.is_eq(ws, vs))

# the maps a and b are the same: entry by entry, in the same shape
def Files.Crit.same(a: Crits.Crit<Files.Item>, b: Crits.Crit<Files.Item>) -> Bool:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Leaf{k2, v2}:
      Bool.and(Crits.Key.is_eq(k1, k2), Files.Item.same(v1, v2))
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      Bool.and(
        Crits.Key.is_eq(r1, r2),
        Bool.and(
          Nat.is_eq(p1, p2),
          Bool.and(
            Shared.Maybe.is_eq(~Files.Item, ~Files.Item.same, e1, e2),
            Bool.and(Files.Crit.same(z1, z2), Files.Crit.same(o1, o2))
          )
        )
      )
    case _ _:
      False{}

# the contents a and b are the same
def Files.same(a: Files, b: Files) -> Bool:
  match a b:
    case Files{x} Files{y}:
      Files.Crit.same(x, y)

# m is the content x
def Files.fits(m: Maybe<&2, Files>, x: Files) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      Files.same(y, x)
