import Base
import ./bools.bend as Bools
import ./shared.bend as Shared

# dropping nothing keeps a list
def List.drop_zero(a, -A: Kind(a), xs: List<a, A>) -> {List.drop(a, A, xs, 0n) == xs: List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# appending nothing keeps a list
def List.append_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, []) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %List.append_nil(A, t): {h <> List.append(&2, A, t, []) == h <> _: List<&2, A>}
      {==}

# dropping the first list of an append leaves the second
def List.drop_after_append(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>
) -> {List.drop(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == ys: List<&2, A>}:
  match xs:
    case Nil{}:
      List.drop_zero(&2, A, ys)
    case Con{h, t}:
      List.drop_after_append(A, t, ys)

# appends group either way
def List.append_assoc(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>,
  zs: List<&2, A>
) -> {
  List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %List.append_assoc(A, t, ys, zs) :
        {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _: List<&2, A>}
      {==}

# the first n elements, then the rest, are the list
def List.take_drop(-A: Data, xs: List<&2, A>, n: Nat) -> {List.append(&2, A, List.take(&2, A, xs, n), List.drop(&2, A, xs, n)) == xs: List<&2, A>}:
  match xs n:
    case Nil{} k:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %List.take_drop(A, t, p) : {h <> List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, p)) == h <> _: List<&2, A>}
      {==}

# Forks
# -----
# Where two lists agree from the start (a fork), and where they agree to the
# end (their ends), as same calls their elements equal.

# the start that two lists share (same), then the rest of each (a and b)
type Fork<-A: Data> is Data:
  Fork{same: List<&2, A>, a: List<&2, A>, b: List<&2, A>}

# the first list of a fork, again
def Fork.left(-A: Data, f: Fork<A>) -> List<&2, A>:
  match f:
    case Fork{s, a, b}:
      List.append(&2, A, s, a)

# the second list of a fork, again
def Fork.right(-A: Data, f: Fork<A>) -> List<&2, A>:
  match f:
    case Fork{s, a, b}:
      List.append(&2, A, s, b)

# the fork of x <> ra and y <> rb, by whether x and y are the same (held); f is
# the fork of ra and rb
def List.fork.on(-A: Data, held: Bool, x: A, y: A, ra: List<&2, A>, rb: List<&2, A>, f: Fork<A>) -> Fork<A>:
  match held f:
    case True{} Fork{s, fa, fb}:
      Fork{x <> s, fa, fb}
    case False{} g:
      Fork{[], x <> ra, y <> rb}

# the start that a and b share, then the rest of each
def List.fork(~A: Data, ~same: A -> A -> Bool, a: List<&2, A>, b: List<&2, A>) -> Fork<A>:
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork.on(A, same(x, y), x, y, ra, rb, List.fork(~A, ~same, ra, rb))
    case Nil{} y:
      Fork{[], [], y}
    case Con{x, ra} Nil{}:
      Fork{[], x <> ra, []}

# the ends that two lists share (same), after what comes before it in each (a
# and b)
type Ends<-A: Data> is Data:
  Ends{a: List<&2, A>, b: List<&2, A>, same: List<&2, A>}

# the first list of its ends, again
def Ends.left(-A: Data, e: Ends<A>) -> List<&2, A>:
  match e:
    case Ends{a, b, s}:
      List.append(&2, A, a, s)

# the second list of its ends, again
def Ends.right(-A: Data, e: Ends<A>) -> List<&2, A>:
  match e:
    case Ends{a, b, s}:
      List.append(&2, A, b, s)

# the ends of x <> ra and y <> rb, by whether x and y are the same (held); e
# are the ends of ra and rb
def List.tails.on(-A: Data, held: Bool, x: A, y: A, e: Ends<A>) -> Ends<A>:
  match held e:
    case True{} Ends{Nil{}, Nil{}, s}:
      Ends{[], [], x <> s}
    case h Ends{ea, eb, s}:
      Ends{x <> ea, y <> eb, s}

# the ends that a and b share, with the lists lined up from their start
def List.tails(~A: Data, ~same: A -> A -> Bool, a: List<&2, A>, b: List<&2, A>) -> Ends<A>:
  match a b:
    case Con{+x, ra} Con{+y, rb}:
      List.tails.on(A, same(x, y), x, y, List.tails(~A, ~same, ra, rb))
    case Nil{} y:
      Ends{[], y, []}
    case Con{x, ra} Nil{}:
      Ends{x <> ra, [], []}

# e, after a comes before its first list and b before its second
def Ends.after(-A: Data, a: List<&2, A>, b: List<&2, A>, e: Ends<A>) -> Ends<A>:
  match e:
    case Ends{ea, eb, s}:
      Ends{List.append(&2, A, a, ea), List.append(&2, A, b, eb), s}

# the ends that a and b share, with the lists lined up at their end
def List.ends(~A: Data, ~same: A -> A -> Bool, +a: List<&2, A>, +b: List<&2, A>) -> Ends<A>:
  +da = Nat.sub(List.length(&2, A, a), List.length(&2, A, b))
  +db = Nat.sub(List.length(&2, A, b), List.length(&2, A, a))
  Ends.after(
    A,
    List.take(&2, A, a, da),
    List.take(&2, A, b, db),
    List.tails(~A, ~same, List.drop(&2, A, a, da), List.drop(&2, A, b, db))
  )

# Laws
# ----
# Each law asks of same only that it is True only for equal elements (sound).

# List.fork_left after the first elements
def List.fork_left.on(
  -A: Data,
  held: Bool,
  x: A,
  y: A,
  ra: List<&2, A>,
  rb: List<&2, A>,
  f: Fork<A>,
  ih: {Fork.left(A, f) == ra: List<&2, A>}
) -> {Fork.left(A, List.fork.on(A, held, x, y, ra, rb, f)) == x <> ra: List<&2, A>}:
  match held f:
    case True{} Fork{s, fa, fb}:
      %ih : {x <> List.append(&2, A, s, fa) == x <> _: List<&2, A>}
      {==}
    case False{} g:
      {==}

# a fork gives back the first list
law List.fork_left:
  for ~A: Data
  for ~same: A -> A -> Bool
  for a: List<&2, A>
  for b: List<&2, A>
  {Fork.left(A, List.fork(~A, ~same, a, b)) == a: List<&2, A>}

def List.fork_left(A, same, a, b):
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork_left.on(A, same(x, y), x, y, ra, rb, List.fork(~A, ~same, ra, rb), List.fork_left(~A, ~same, ra, rb))
    case Nil{} y:
      {==}
    case Con{x, ra} Nil{}:
      {==}

# List.fork_right after the first elements
def List.fork_right.on(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A},
  held: Bool,
  +x: A,
  +y: A,
  ra: List<&2, A>,
  rb: List<&2, A>,
  f: Fork<A>,
  e: {same(x, y) == held: Bool},
  ih: {Fork.right(A, f) == rb: List<&2, A>}
) -> {Fork.right(A, List.fork.on(A, held, x, y, ra, rb, f)) == y <> rb: List<&2, A>}:
  match held f:
    case True{} Fork{s, fa, fb}:
      %ih : {x <> List.append(&2, A, s, fb) == y <> _: List<&2, A>}
      %sound(x)(y)(e) : {x <> List.append(&2, A, s, fb) == _ <> List.append(&2, A, s, fb): List<&2, A>}
      {==}
    case False{} g:
      {==}

# a fork gives back the second list
law List.fork_right:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A}
  for a: List<&2, A>
  for b: List<&2, A>
  {Fork.right(A, List.fork(~A, ~same, a, b)) == b: List<&2, A>}

def List.fork_right(A, same, sound, a, b):
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.fork_right.on(
        ~A,
        ~same,
        ~sound,
        same(x, y),
        x,
        y,
        ra,
        rb,
        List.fork(~A, ~same, ra, rb),
        {==},
        List.fork_right(~A, ~same, ~sound, ra, rb)
      )
    case Nil{} y:
      {==}
    case Con{x, ra} Nil{}:
      {==}

# List.tails_left after the first elements
def List.tails_left.on(
  -A: Data,
  held: Bool,
  x: A,
  y: A,
  ra: List<&2, A>,
  e: Ends<A>,
  ih: {Ends.left(A, e) == ra: List<&2, A>}
) -> {Ends.left(A, List.tails.on(A, held, x, y, e)) == x <> ra: List<&2, A>}:
  match held e:
    case True{} Ends{Nil{}, Nil{}, s}:
      %ih : {x <> s == x <> _: List<&2, A>}
      {==}
    case True{} Ends{Nil{}, Con{q, qs}, s}:
      %ih : {x <> s == x <> _: List<&2, A>}
      {==}
    case True{} Ends{Con{p, ps}, eb, s}:
      %ih : {x <> List.append(&2, A, p <> ps, s) == x <> _: List<&2, A>}
      {==}
    case False{} Ends{ea, eb, s}:
      %ih : {x <> List.append(&2, A, ea, s) == x <> _: List<&2, A>}
      {==}

# the ends of two lists give back the first
law List.tails_left:
  for ~A: Data
  for ~same: A -> A -> Bool
  for a: List<&2, A>
  for b: List<&2, A>
  {Ends.left(A, List.tails(~A, ~same, a, b)) == a: List<&2, A>}

def List.tails_left(A, same, a, b):
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.tails_left.on(A, same(x, y), x, y, ra, List.tails(~A, ~same, ra, rb), List.tails_left(~A, ~same, ra, rb))
    case Nil{} y:
      {==}
    case Con{x, ra} Nil{}:
      List.append_nil(A, x <> ra)

# List.tails_right after the first elements
def List.tails_right.on(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A},
  held: Bool,
  +x: A,
  +y: A,
  rb: List<&2, A>,
  e: Ends<A>,
  h: {same(x, y) == held: Bool},
  ih: {Ends.right(A, e) == rb: List<&2, A>}
) -> {Ends.right(A, List.tails.on(A, held, x, y, e)) == y <> rb: List<&2, A>}:
  match held e:
    case True{} Ends{Nil{}, Nil{}, s}:
      %ih : {x <> s == y <> _: List<&2, A>}
      %sound(x)(y)(h) : {x <> s == _ <> s: List<&2, A>}
      {==}
    case True{} Ends{Nil{}, Con{q, qs}, s}:
      %ih : {y <> List.append(&2, A, q <> qs, s) == y <> _: List<&2, A>}
      {==}
    case True{} Ends{Con{p, ps}, eb, s}:
      %ih : {y <> List.append(&2, A, eb, s) == y <> _: List<&2, A>}
      {==}
    case False{} Ends{ea, eb, s}:
      %ih : {y <> List.append(&2, A, eb, s) == y <> _: List<&2, A>}
      {==}

# the ends of two lists give back the second
law List.tails_right:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A}
  for a: List<&2, A>
  for b: List<&2, A>
  {Ends.right(A, List.tails(~A, ~same, a, b)) == b: List<&2, A>}

def List.tails_right(A, same, sound, a, b):
  match a b:
    case Con{+x, +ra} Con{+y, +rb}:
      List.tails_right.on(
        ~A,
        ~same,
        ~sound,
        same(x, y),
        x,
        y,
        rb,
        List.tails(~A, ~same, ra, rb),
        {==},
        List.tails_right(~A, ~same, ~sound, ra, rb)
      )
    case Nil{} y:
      List.append_nil(A, y)
    case Con{x, ra} Nil{}:
      {==}

# the first list of e after a comes before it is a, then the first list of e
def Ends.after_left(-A: Data, a: List<&2, A>, b: List<&2, A>, e: Ends<A>) -> {Ends.left(A, Ends.after(A, a, b, e)) == List.append(&2, A, a, Ends.left(A, e)): List<&2, A>}:
  match e:
    case Ends{ea, eb, s}:
      List.append_assoc(A, a, ea, s)

# the second list of e after b comes before it is b, then the second list of e
def Ends.after_right(-A: Data, a: List<&2, A>, b: List<&2, A>, e: Ends<A>) -> {Ends.right(A, Ends.after(A, a, b, e)) == List.append(&2, A, b, Ends.right(A, e)): List<&2, A>}:
  match e:
    case Ends{ea, eb, s}:
      List.append_assoc(A, b, eb, s)

# the ends of two lists, lined up at their end, give back the first
law List.ends_left:
  for ~A: Data
  for ~same: A -> A -> Bool
  for +a: List<&2, A>
  for +b: List<&2, A>
  {Ends.left(A, List.ends(~A, ~same, a, b)) == a: List<&2, A>}

def List.ends_left(A, same, a, b):
  +da = Nat.sub(List.length(&2, A, a), List.length(&2, A, b))
  +db = Nat.sub(List.length(&2, A, b), List.length(&2, A, a))
  +pa = List.take(&2, A, a, da)
  +ra = List.drop(&2, A, a, da)
  +rb = List.drop(&2, A, b, db)
  +t = List.tails(~A, ~same, ra, rb)
  Equal.trans(
    List<&2, A>,
    Ends.left(A, Ends.after(A, pa, List.take(&2, A, b, db), t)),
    List.append(&2, A, pa, Ends.left(A, t)),
    a,
    Ends.after_left(A, pa, List.take(&2, A, b, db), t),
    Equal.trans(
      List<&2, A>,
      List.append(&2, A, pa, Ends.left(A, t)),
      List.append(&2, A, pa, ra),
      a,
      Equal.cong(List<&2, A>, List<&2, A>, z => List.append(&2, A, pa, z), Ends.left(A, t), ra, List.tails_left(~A, ~same, ra, rb)),
      List.take_drop(A, a, da)
    )
  )

# the ends of two lists, lined up at their end, give back the second
law List.ends_right:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A}
  for +a: List<&2, A>
  for +b: List<&2, A>
  {Ends.right(A, List.ends(~A, ~same, a, b)) == b: List<&2, A>}

def List.ends_right(A, same, sound, a, b):
  +da = Nat.sub(List.length(&2, A, a), List.length(&2, A, b))
  +db = Nat.sub(List.length(&2, A, b), List.length(&2, A, a))
  +pb = List.take(&2, A, b, db)
  +ra = List.drop(&2, A, a, da)
  +rb = List.drop(&2, A, b, db)
  +t = List.tails(~A, ~same, ra, rb)
  Equal.trans(
    List<&2, A>,
    Ends.right(A, Ends.after(A, List.take(&2, A, a, da), pb, t)),
    List.append(&2, A, pb, Ends.right(A, t)),
    b,
    Ends.after_right(A, List.take(&2, A, a, da), pb, t),
    Equal.trans(
      List<&2, A>,
      List.append(&2, A, pb, Ends.right(A, t)),
      List.append(&2, A, pb, rb),
      b,
      Equal.cong(List<&2, A>, List<&2, A>, z => List.append(&2, A, pb, z), Ends.right(A, t), rb, List.tails_right(~A, ~same, ~sound, ra, rb)),
      List.take_drop(A, b, db)
    )
  )

# Equality
# --------

# xs and ys hold the same elements in the same order, as same calls them
def List.same(~A: Data, ~same: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(same(x, y), List.same(~A, ~same, xr, yr))
    case _ _:
      False{}

# List.same is True for a list and itself
law List.same_refl:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~refl: @x: A -> {same(x, x) == True{}: Bool}
  for xs: List<&2, A>
  {List.same(~A, ~same, xs, xs) == True{}: Bool}

def List.same_refl(A, same, refl, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Bool, same(x, x), True{}, refl(x)) : {Bool.and(_, List.same(~A, ~same, r, r)) == True{}: Bool}
      List.same_refl(~A, ~same, ~refl, r)

# List.same is True only for equal lists
law List.same_sound:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~sound: @x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A}
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.same(~A, ~same, xs, ys) == True{}: Bool} -> {xs == ys: List<&2, A>}

def List.same_sound(A, same, sound, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yr}:
      h => Empty.absurd({Nil{} == Con{y, yr}: List<&2, A>}, Shared.Bool.false_ne_true(h))
    case Con{x, xr} Nil{}:
      h => Empty.absurd({Con{x, xr} == Nil{}: List<&2, A>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xr} Con{+y, +yr}:
      +h =>
        %sound(x)(y)(Bools.Bool.and_true_left(same(x, y), List.same(~A, ~same, xr, yr))(h)) : {x <> xr == _ <> yr: List<&2, A>}
        %List.same_sound(~A, ~same, ~sound, xr, yr)(Bools.Bool.and_true_right(same(x, y), List.same(~A, ~same, xr, yr))(h)) :
          {x <> xr == x <> _: List<&2, A>}
        {==}

# the first elements of xs ++ ys, as many as xs has, are xs
def List.take_append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> {List.take(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case Con{h, t}:
      %List.take_append(A, t, ys) : {h <> List.take(&2, A, List.append(&2, A, t, ys), List.length(&2, A, t)) == h <> _: List<&2, A>}
      {==}
