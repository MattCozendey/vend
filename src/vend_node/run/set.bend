import Base
import ../../shared/shared/shared/shared/crit.bend as Crits

# The check of a set of values
# ----------------------------
# A set of values is a crit-bit map from the key of each value to the value.
# This is the check that each value of a map sits under its own key: plain
# code, with no proof. The laws of sets are in shared/set.bend.

# the end e of a fork with rep r, if any, sits under its own key
def ValSet.ok.end(~A: Data, ~key: A -> List<&2, U32>, r: List<&2, U32>, e: Maybe<&2, A>) -> Bool:
  match e:
    case None{}:
      True{}
    case Some{v}:
      Crits.Key.is_eq(r, key(v))

# each value of the map m sits under its own key
def ValSet.ok(~A: Data, ~key: A -> List<&2, U32>, m: Crits.Crit<A>) -> Bool:
  match m:
    case Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k, v}:
      Crits.Key.is_eq(k, key(v))
    case Crits.Crit.Fork{r, p, e, z, o}:
      Bool.and(
        ValSet.ok.end(~A, ~key, r, e),
        Bool.and(ValSet.ok(~A, ~key, z), ValSet.ok(~A, ~key, o))
      )
