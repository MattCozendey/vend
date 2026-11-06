import Base

# Conditions: when an edge of the graph is active. A condition is a Boolean
# formula over named atoms ("_WIN32", "TEST", ...). A configuration says
# which atoms hold. One graph carries every condition, so no configuration
# is ever enumerated: a question about many configurations is a question
# about one formula.

# A condition.
type Cond is Data:
  Always{}
  Never{}
  Atom{name: String}
  Not{c: Cond}
  And{a: Cond, b: Cond}
  Or{a: Cond, b: Cond}

# A configuration: the atoms that hold; every other atom does not hold.
type Config is Data:
  Config{on: List<&2, String>}

# atom n holds in cfg
def Config.has(cfg: Config, n: String) -> Bool:
  match cfg:
    case Config{on}:
      List.contains(~String, ~String.eq, on, n)

# c holds in cfg
def Cond.holds(c: Cond, +cfg: Config) -> Bool:
  match c:
    case Always{}:
      True{}
    case Never{}:
      False{}
    case Atom{n}:
      Config.has(cfg, n)
    case Not{x}:
      Bool.not(Cond.holds(x, cfg))
    case And{a, b}:
      List.all.if(u => Cond.holds(b, cfg), Cond.holds(a, cfg))
    case Or{a, b}:
      List.any.if(u => Cond.holds(b, cfg), Cond.holds(a, cfg))

# a and b hold in the same configurations
def Cond.Same(a: Cond, b: Cond) -> Type:
  @cfg: Config -> {Cond.holds(a, cfg) == Cond.holds(b, cfg): Bool}

# The answer to: is there a configuration where it holds? Unlike a glob
# search, this one always finishes: only the atoms that the formula names
# matter, and they are finitely many.
type Sat is Data:
  Holds{cfg: Config}
  Unsat{}

# a configuration where c holds, or Unsat
law Cond.sat:
  for c: Cond
  Sat

# a Holds answer names a configuration where c holds
law sat_holds:
  for c: Cond
  for cfg: Config
  for h: {Cond.sat(c) == Holds{cfg}: Sat}
  {Cond.holds(c, cfg) == True{}: Bool}

# after Unsat, c holds in no configuration
law sat_unsat:
  for c: Cond
  for cfg: Config
  for h: {Cond.sat(c) == Unsat{}: Sat}
  {Cond.holds(c, cfg) == False{}: Bool}

# Overlap and coverage are questions to Cond.sat: a and b can hold together
# when And{a, b} holds somewhere, and a covers b when And{b, Not{a}} holds
# nowhere.

# The canonical form of a condition: two conditions that hold in the same
# configurations get the same form, so equal meaning is equal data, and a
# graph can compare and share conditions cheaply.
law Cond.canon:
  for c: Cond
  Cond

# the canonical form means what the condition means
law canon_same:
  for c: Cond
  Cond.Same(Cond.canon(c), c)

# conditions with the same meaning have one canonical form
law canon_unique:
  for a: Cond
  for b: Cond
  for s: Cond.Same(a, b)
  {Cond.canon(a) == Cond.canon(b): Cond}

# a and b are the same formula, written the same way
def Cond.is_eq(a: Cond, b: Cond) -> Bool:
  match a b:
    case Always{} Always{}:
      True{}
    case Never{} Never{}:
      True{}
    case Atom{x} Atom{y}:
      String.eq(x, y)
    case Not{x} Not{y}:
      Cond.is_eq(x, y)
    case And{a1, b1} And{a2, b2}:
      List.all.if(u => Cond.is_eq(b1, b2), Cond.is_eq(a1, a2))
    case Or{a1, b1} Or{a2, b2}:
      List.all.if(u => Cond.is_eq(b1, b2), Cond.is_eq(a1, a2))
    case _ _:
      False{}

# Sat answers Holds
def Sat.is_holds(s: Sat) -> Bool:
  match s:
    case Holds{cfg}:
      True{}
    case Unsat{}:
      False{}
