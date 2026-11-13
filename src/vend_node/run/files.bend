import Base
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes

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
