import Base
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes

# Parts
# -----
# Content stored once by hash: a plain crit-bit map from the code of a hash to
# words, and no proof is built when it changes. A read hashes what it finds
# and answers only when that is the hash asked, so an entry under a wrong key
# holds nothing. The laws are in shared/parts.bend, said of the same map with
# the proof that it is well formed (Parts.wf), which each def here keeps.

# the parts: words, each under the code of its hash
type Parts is Data:
  Parts{crit: Crits.Crit<List<&2, U32>>}

# the key of the hash h: its code
def Parts.key(h: Hashes.Hash) -> List<&2, U32>:
  Hashes.Hash.code(h, [])

# the words m, when their hash is h
def Parts.get.of(m: Maybe<&2, List<&2, U32>>, h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{+ws}:
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
        Some{ws},
        None{}
      )

# the words of the hash h in d
def Parts.get(d: Parts, +h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  match d:
    case Parts{t}:
      Parts.get.of(Crits.Crit.get(List<&2, U32>, t, Parts.key(h)), h)

# no part
def Parts.new() -> Parts:
  Parts{Crits.Crit.new(List<&2, U32>)}

# d with the words ws under the hash h, unless d holds h
def Parts.put.if(held: Bool, d: Parts, h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  match held d:
    case True{} d:
      d
    case False{} Parts{t}:
      Parts{Crits.Crit.set(~List<&2, U32>, t, Parts.key(h), ws)}

# d with the words ws under their hash h: what d holds under it stays
def Parts.put.at(d: Parts, +h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  +d = d
  Parts.put.if(Maybe.is_some(&2, List<&2, U32>, Parts.get(d, h)), d, h, ws)

# d with the words ws under their hash: what d holds under it stays
def Parts.put(d: Parts, +ws: List<&2, U32>) -> Parts:
  Parts.put.at(d, Hashes.Sha.hash(ws), ws)

# rest, after the hash h when hit
def Parts.list.if(hit: Bool, h: Hashes.Hash, rest: List<&2, Hashes.Hash>) -> List<&2, Hashes.Hash>:
  match hit:
    case True{}:
      h <> rest
    case False{}:
      rest

# the hashes of the entries es whose key is the code of their hash
def Parts.list.go(es: List<&2, Crits.Bind<List<&2, U32>>>) -> List<&2, Hashes.Hash>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{k, ws}, r}:
      +h = Hashes.Sha.hash(ws)
      Parts.list.if(Crits.Key.is_eq(k, Parts.key(h)), h, Parts.list.go(r))

# rest, after the hash h unless it was seen
def Parts.uniq.cons(
  was: Bool,
  h: Hashes.Hash,
  rest: List<&2, Hashes.Hash>
) -> List<&2, Hashes.Hash>:
  match was:
    case True{}:
      rest
    case False{}:
      h <> rest

# the seen keys s, with k unless it was seen
def Parts.uniq.seen(was: Bool, s: Crits.Crit<Unit>, k: List<&2, U32>) -> Crits.Crit<Unit>:
  match was:
    case True{}:
      s
    case False{}:
      Crits.Crit.set(~Unit, s, k, Unit{})

# the hashes hs, each once, but for those whose key is in seen
def Parts.uniq(hs: List<&2, Hashes.Hash>, +seen: Crits.Crit<Unit>) -> List<&2, Hashes.Hash>:
  match hs:
    case Nil{}:
      []
    case Con{+h, r}:
      Parts.uniq.cons(
        Crits.Crit.has(Unit, seen, Parts.key(h)),
        h,
        Parts.uniq(r, Parts.uniq.seen(Crits.Crit.has(Unit, seen, Parts.key(h)), seen, Parts.key(h)))
      )

# the hashes held in d, each once
def Parts.list(d: Parts) -> List<&2, Hashes.Hash>:
  match d:
    case Parts{t}:
      Parts.uniq(Parts.list.go(Crits.Crit.entries(List<&2, U32>, t)), Crits.Crit.new(Unit))

# a with the words ws under their hash h, when hit
def Parts.join.add(hit: Bool, a: Parts, h: Hashes.Hash, ws: List<&2, U32>) -> Parts:
  match hit:
    case True{}:
      Parts.put.at(a, h, ws)
    case False{}:
      a

# a with the words of each of the entries es whose key is the code of their hash
def Parts.join.go(es: List<&2, Crits.Bind<List<&2, U32>>>, a: Parts) -> Parts:
  match es:
    case Nil{}:
      a
    case Con{Crits.Bind{k, +ws}, r}:
      Parts.join.go(
        r,
        Parts.join.add(
          Crits.Key.is_eq(k, Parts.key(Hashes.Sha.hash(ws))),
          a,
          Hashes.Sha.hash(ws),
          ws
        )
      )

# a with each part of b: what a holds stays
def Parts.join(a: Parts, b: Parts) -> Parts:
  match b:
    case Parts{t}:
      Parts.join.go(Crits.Crit.entries(List<&2, U32>, t), a)

# acc with the words m, if any, under the hash h
def Parts.only.add(m: Maybe<&2, List<&2, U32>>, h: Hashes.Hash, acc: Parts) -> Parts:
  match m acc:
    case None{} acc:
      acc
    case Some{ws} Parts{t}:
      Parts{Crits.Crit.set(~List<&2, U32>, t, Parts.key(h), ws)}

# the parts of d whose hash is in hs
def Parts.only.go(hs: List<&2, Hashes.Hash>, +d: Parts) -> Parts:
  match hs:
    case Nil{}:
      Parts.new()
    case Con{+h, r}:
      Parts.only.add(Parts.get(d, h), h, Parts.only.go(r, d))

# the parts of d whose hash is in hs
def Parts.only(d: Parts, hs: List<&2, Hashes.Hash>) -> Parts:
  Parts.only.go(hs, d)

# the map of the parts d is well formed: what the laws of parts ask for. The
# code that runs keeps it and builds no proof of it
def Parts.wf(d: Parts) -> Bool:
  match d:
    case Parts{t}:
      Crits.Crit.wf(~List<&2, U32>, t, 0n)
