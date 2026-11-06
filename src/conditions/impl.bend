import Base
import ../shared.bend as Shared
import ./spec.bend as Spec

# Cond.sat tries every assignment of the atoms that the formula names
# (2^k for k atoms) and stops at the first that holds; atoms the formula
# does not name do not change its value.

# the atom names of c, each once, before seen
def Cond.atoms(c: Spec.Cond, +seen: List<&2, String>) -> List<&2, String>:
  match c:
    case Spec.Always{}:
      seen
    case Spec.Never{}:
      seen
    case Spec.Atom{+n}:
      Shared.Bool.when(
        List<&2, String>,
        List.contains(~String, ~String.eq, seen, n),
        u => seen,
        u => n <> seen
      )
    case Spec.Not{x}:
      Cond.atoms(x, seen)
    case Spec.And{a, b}:
      Cond.atoms(b, Cond.atoms(a, seen))
    case Spec.Or{a, b}:
      Cond.atoms(b, Cond.atoms(a, seen))

# m, or else k()
def Cond.first(
  m: Maybe<&2, Spec.Config>,
  k: Unit -> Maybe<&2, Spec.Config>
) -> Maybe<&2, Spec.Config>:
  match m:
    case None{}:
      k(Unit{})
    case Some{cfg}:
      Some{cfg}

# a configuration where c holds, with the atoms of on holding, each atom
# of atoms either holding or not, and every other atom not holding
def Cond.search(
  atoms: List<&2, String>,
  +c: Spec.Cond,
  +on: List<&2, String>
) -> Maybe<&2, Spec.Config>:
  match atoms:
    case Nil{}:
      Shared.Bool.when(
        Maybe<&2, Spec.Config>,
        Spec.Cond.holds(c, Spec.Config{on}),
        u => Some{Spec.Config{on}},
        u => None{}
      )
    case Con{a, +t}:
      Cond.first(Cond.search(t, c, a <> on), u => Cond.search(t, c, on))

# Holds for a configuration, Unsat for none
def Cond.answer(m: Maybe<&2, Spec.Config>) -> Spec.Sat:
  match m:
    case None{}:
      Spec.Unsat{}
    case Some{cfg}:
      Spec.Holds{cfg}

def Spec.Cond.sat(c):
  +c = c
  Cond.answer(Cond.search(Cond.atoms(c, []), c, []))
