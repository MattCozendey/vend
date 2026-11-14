import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Strings
import ./spec.bend as Spec
import ./types.bend as Types

# The codes of the core of a Vend Node
# ------------------------------------
# Requests, picks, steps and facts are named by their codes (Codes): a value
# is its words, and two values are equal exactly when their words are.

# the code of counts
def Count.codec() -> Codes.Codec(Nat):
  (Codes.Code.count, (Codes.Code.count.read, x => r => Codes.Code.count_read(x, r)))

# texts x, then r
def Texts.code(x: List<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~String, ~Codes.Code.text, x, r)

# texts
def Texts.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, String>>>:
  Codes.Code.list.read(~String, ~Codes.Code.text.read, ts)

# the code of texts
def Texts.codec() -> Codes.Codec(List<&2, String>):
  Codes.Code.list.codec(~String, ~Codes.Code.text.codec())

# words, if any, x, then r
def Content.code(x: Maybe<&2, List<&2, U32>>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~List<&2, U32>, ~Codes.Code.words, x, r)

# words, if any,
def Content.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, List<&2, U32>>>>:
  Codes.Code.maybe.read(~List<&2, U32>, ~Codes.Code.words.read, ts)

# the code of words, if any,
def Content.codec() -> Codes.Codec(Maybe<&2, List<&2, U32>>):
  Codes.Code.maybe.codec(~List<&2, U32>, ~Codes.Code.words.codec())

# the request x, then r
def Request.code(x: Spec.Request, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Spec.Request.Start{x0}:
      0 <> Texts.code(x0, r)
    case Spec.Request.Write{x0, x1, x2}:
      1 <> Ledgers.Line.code(x0, Codes.Code.text(x1, Content.code(x2, r)))
    case Spec.Request.Merge{x0, x1}:
      2 <> Ledgers.Line.code(x0, Ledgers.Line.code(x1, r))
    case Spec.Request.Resolve{x0, x1, x2}:
      3 <> Ledgers.Id.code(x0, Codes.Code.text(x1, Content.code(x2, r)))
    case Spec.Request.Mark{x0, x1, x2}:
      4 <> Ledgers.Line.code(x0, Codes.Code.text(x1, Codes.Code.count(x2, r)))
    case Spec.Request.Move{x0, x1, x2}:
      5 <> Ledgers.Line.code(x0, Ledgers.Line.code(x1, Codes.Code.count(x2, r)))
    case Spec.Request.Group{x0, x1, x2}:
      6 <> Hashes.Hash.code(x0, Codes.Code.text(x1, Texts.code(x2, r)))
    case Spec.Request.Own{x0, x1}:
      7 <> Ledgers.Line.code(x0, Codes.Code.text(x1, r))

# a request whose tag is x, from the tokens r after it
def Request.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Spec.Request>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Spec.Request>>,
    U32.is_eq(x, 0),
    u => Codes.Code.one.read(
      ~List<&2, String>,
      ~Spec.Request,
      ~Texts.code.read,
      a => Spec.Request.Start{a},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Spec.Request>>,
      U32.is_eq(x, 1),
      u => Codes.Code.three.read(
        ~Ledgers.Line,
        ~String,
        ~Maybe<&2, List<&2, U32>>,
        ~Spec.Request,
        ~Ledgers.Line.code.read,
        ~Codes.Code.text.read,
        ~Content.code.read,
        a => b => c => Spec.Request.Write{a, b, c},
        r
      ),
      u => Shared.Bool.when(
        Maybe<&2, Codes.Read<Spec.Request>>,
        U32.is_eq(x, 2),
        u => Codes.Code.two.read(
          ~Ledgers.Line,
          ~Ledgers.Line,
          ~Spec.Request,
          ~Ledgers.Line.code.read,
          ~Ledgers.Line.code.read,
          a => b => Spec.Request.Merge{a, b},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Spec.Request>>,
          U32.is_eq(x, 3),
          u => Codes.Code.three.read(
            ~Ledgers.Id,
            ~String,
            ~Maybe<&2, List<&2, U32>>,
            ~Spec.Request,
            ~Ledgers.Id.code.read,
            ~Codes.Code.text.read,
            ~Content.code.read,
            a => b => c => Spec.Request.Resolve{a, b, c},
            r
          ),
          u => Shared.Bool.when(
            Maybe<&2, Codes.Read<Spec.Request>>,
            U32.is_eq(x, 4),
            u => Codes.Code.three.read(
              ~Ledgers.Line,
              ~String,
              ~Nat,
              ~Spec.Request,
              ~Ledgers.Line.code.read,
              ~Codes.Code.text.read,
              ~Codes.Code.count.read,
              a => b => c => Spec.Request.Mark{a, b, c},
              r
            ),
            u => Shared.Bool.when(
              Maybe<&2, Codes.Read<Spec.Request>>,
              U32.is_eq(x, 5),
              u => Codes.Code.three.read(
                ~Ledgers.Line,
                ~Ledgers.Line,
                ~Nat,
                ~Spec.Request,
                ~Ledgers.Line.code.read,
                ~Ledgers.Line.code.read,
                ~Codes.Code.count.read,
                a => b => c => Spec.Request.Move{a, b, c},
                r
              ),
              u => Shared.Bool.when(
                Maybe<&2, Codes.Read<Spec.Request>>,
                U32.is_eq(x, 6),
                u => Codes.Code.three.read(
                  ~Hashes.Hash,
                  ~String,
                  ~List<&2, String>,
                  ~Spec.Request,
                  ~Hashes.Hash.code.read,
                  ~Codes.Code.text.read,
                  ~Texts.code.read,
                  a => b => c => Spec.Request.Group{a, b, c},
                  r
                ),
                u => Shared.Bool.when(
                  Maybe<&2, Codes.Read<Spec.Request>>,
                  U32.is_eq(x, 7),
                  u => Codes.Code.two.read(
                    ~Ledgers.Line,
                    ~String,
                    ~Spec.Request,
                    ~Ledgers.Line.code.read,
                    ~Codes.Code.text.read,
                    a => b => Spec.Request.Own{a, b},
                    r
                  ),
                  u => None{}
                )
              )
            )
          )
        )
      )
    )
  )

# a request
def Request.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Spec.Request>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Request.code.read.of(x, r)

# a request reads back
def Request.code_read(
  x: Spec.Request,
  r: List<&2, U32>
) -> {
  Request.code.read(
    Request.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Request>>
}:
  match x:
    case Spec.Request.Start{x0}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Request,
        ~Texts.codec(),
        a => Spec.Request.Start{a},
        x0,
        r
      )
    case Spec.Request.Write{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Line,
        ~String,
        ~Maybe<&2, List<&2, U32>>,
        ~Spec.Request,
        ~Ledgers.Line.codec(),
        ~Codes.Code.text.codec(),
        ~Content.codec(),
        a => b => c => Spec.Request.Write{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Spec.Request.Merge{x0, x1}:
      Codes.Code.two_read(
        ~Ledgers.Line,
        ~Ledgers.Line,
        ~Spec.Request,
        ~Ledgers.Line.codec(),
        ~Ledgers.Line.codec(),
        a => b => Spec.Request.Merge{a, b},
        x0,
        x1,
        r
      )
    case Spec.Request.Resolve{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~String,
        ~Maybe<&2, List<&2, U32>>,
        ~Spec.Request,
        ~Ledgers.Id.codec(),
        ~Codes.Code.text.codec(),
        ~Content.codec(),
        a => b => c => Spec.Request.Resolve{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Spec.Request.Mark{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Line,
        ~String,
        ~Nat,
        ~Spec.Request,
        ~Ledgers.Line.codec(),
        ~Codes.Code.text.codec(),
        ~Count.codec(),
        a => b => c => Spec.Request.Mark{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Spec.Request.Move{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Line,
        ~Ledgers.Line,
        ~Nat,
        ~Spec.Request,
        ~Ledgers.Line.codec(),
        ~Ledgers.Line.codec(),
        ~Count.codec(),
        a => b => c => Spec.Request.Move{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Spec.Request.Group{x0, x1, x2}:
      Codes.Code.three_read(
        ~Hashes.Hash,
        ~String,
        ~List<&2, String>,
        ~Spec.Request,
        ~Hashes.Hash.codec(),
        ~Codes.Code.text.codec(),
        ~Texts.codec(),
        a => b => c => Spec.Request.Group{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Spec.Request.Own{x0, x1}:
      Codes.Code.two_read(
        ~Ledgers.Line,
        ~String,
        ~Spec.Request,
        ~Ledgers.Line.codec(),
        ~Codes.Code.text.codec(),
        a => b => Spec.Request.Own{a, b},
        x0,
        x1,
        r
      )

# the code of requests
def Request.codec() -> Codes.Codec(Spec.Request):
  (Request.code, (Request.code.read, x => r => Request.code_read(x, r)))

# the version x, then r
def Point.code(x: Spec.Point, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Spec.Point{x0, x1}:
      Ledgers.Line.code(x0, Codes.Code.count(x1, r))

# a version
def Point.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Spec.Point>>:
  Codes.Code.two.read(
    ~Ledgers.Line,
    ~Nat,
    ~Spec.Point,
    ~Ledgers.Line.code.read,
    ~Codes.Code.count.read,
    a => b => Spec.Point{a, b},
    ts
  )

# a version reads back
def Point.code_read(
  x: Spec.Point,
  r: List<&2, U32>
) -> {
  Point.code.read(Point.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Point>>
}:
  match x:
    case Spec.Point{x0, x1}:
      Codes.Code.two_read(
        ~Ledgers.Line,
        ~Nat,
        ~Spec.Point,
        ~Ledgers.Line.codec(),
        ~Count.codec(),
        a => b => Spec.Point{a, b},
        x0,
        x1,
        r
      )

# the code of versions
def Point.codec() -> Codes.Codec(Spec.Point):
  (Point.code, (Point.code.read, x => r => Point.code_read(x, r)))

# a version, if any, x, then r
def Base.code(x: Maybe<&2, Spec.Point>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Spec.Point, ~Point.code, x, r)

# a version, if any,
def Base.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Spec.Point>>>:
  Codes.Code.maybe.read(~Spec.Point, ~Point.code.read, ts)

# the code of a version, if any,
def Base.codec() -> Codes.Codec(Maybe<&2, Spec.Point>):
  Codes.Code.maybe.codec(~Spec.Point, ~Point.codec())

# versions x, then r
def Points.code(x: List<&2, Spec.Point>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Spec.Point, ~Point.code, x, r)

# versions
def Points.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Spec.Point>>>:
  Codes.Code.list.read(~Spec.Point, ~Point.code.read, ts)

# the code of versions
def Points.codec() -> Codes.Codec(List<&2, Spec.Point>):
  Codes.Code.list.codec(~Spec.Point, ~Point.codec())

# the ask x, then r
def Ask.code(x: Types.Ask, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Ask{x0, x1, x2}:
      Ledgers.Id.code(x0, Codes.Code.count(x1, Request.code(x2, r)))

# a ask
def Ask.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Ask>>:
  Codes.Code.three.read(
    ~Ledgers.Id,
    ~Nat,
    ~Spec.Request,
    ~Types.Ask,
    ~Ledgers.Id.code.read,
    ~Codes.Code.count.read,
    ~Request.code.read,
    a => b => c => Types.Ask{a, b, c},
    ts
  )

# a ask reads back
def Ask.code_read(
  x: Types.Ask,
  r: List<&2, U32>
) -> {Ask.code.read(Ask.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Ask>>}:
  match x:
    case Types.Ask{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Nat,
        ~Spec.Request,
        ~Types.Ask,
        ~Ledgers.Id.codec(),
        ~Count.codec(),
        ~Request.codec(),
        a => b => c => Types.Ask{a, b, c},
        x0,
        x1,
        x2,
        r
      )

# the code of asks
def Ask.codec() -> Codes.Codec(Types.Ask):
  (Ask.code, (Ask.code.read, x => r => Ask.code_read(x, r)))

# the pins x, then r
def Pins.code(x: Types.Pins, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Pins{x0, x1, x2, x3, x4}:
      Codes.Code.count(x0, Codes.Code.count(x1, Base.code(x2, Points.code(x3, Points.code(x4, r)))))

# a pins
def Pins.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Pins>>:
  Codes.Code.five.read(
    ~Nat,
    ~Nat,
    ~Maybe<&2, Spec.Point>,
    ~List<&2, Spec.Point>,
    ~List<&2, Spec.Point>,
    ~Types.Pins,
    ~Codes.Code.count.read,
    ~Codes.Code.count.read,
    ~Base.code.read,
    ~Points.code.read,
    ~Points.code.read,
    a => b => c => d => e => Types.Pins{a, b, c, d, e},
    ts
  )

# a pins reads back
def Pins.code_read(
  x: Types.Pins,
  r: List<&2, U32>
) -> {Pins.code.read(Pins.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Pins>>}:
  match x:
    case Types.Pins{x0, x1, x2, x3, x4}:
      Codes.Code.five_read(
        ~Nat,
        ~Nat,
        ~Maybe<&2, Spec.Point>,
        ~List<&2, Spec.Point>,
        ~List<&2, Spec.Point>,
        ~Types.Pins,
        ~Count.codec(),
        ~Count.codec(),
        ~Base.codec(),
        ~Points.codec(),
        ~Points.codec(),
        a => b => c => d => e => Types.Pins{a, b, c, d, e},
        x0,
        x1,
        x2,
        x3,
        x4,
        r
      )

# the code of pinss
def Pins.codec() -> Codes.Codec(Types.Pins):
  (Pins.code, (Pins.code.read, x => r => Pins.code_read(x, r)))

# the pick x, then r
def Pick.code(x: Types.Pick, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Pick{x0, x1}:
      Ask.code(x0, Pins.code(x1, r))

# a pick
def Pick.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Pick>>:
  Codes.Code.two.read(
    ~Types.Ask,
    ~Types.Pins,
    ~Types.Pick,
    ~Ask.code.read,
    ~Pins.code.read,
    a => b => Types.Pick{a, b},
    ts
  )

# a pick reads back
def Pick.code_read(
  x: Types.Pick,
  r: List<&2, U32>
) -> {Pick.code.read(Pick.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Pick>>}:
  match x:
    case Types.Pick{x0, x1}:
      Codes.Code.two_read(
        ~Types.Ask,
        ~Types.Pins,
        ~Types.Pick,
        ~Ask.codec(),
        ~Pins.codec(),
        a => b => Types.Pick{a, b},
        x0,
        x1,
        r
      )

# the code of picks
def Pick.codec() -> Codes.Codec(Types.Pick):
  (Pick.code, (Pick.code.read, x => r => Pick.code_read(x, r)))

# the step x, then r
def Step.code(x: Types.Step, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Step.At{x0, x1, x2}:
      0 <> Ledgers.Line.code(x0, Codes.Code.count(x1, Codes.Code.count(x2, r)))
    case Types.Step.Broken{}:
      1 <> r

# a step whose tag is x, from the tokens r after it
def Step.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Step>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Types.Step>>,
    U32.is_eq(x, 0),
    u => Codes.Code.three.read(
      ~Ledgers.Line,
      ~Nat,
      ~Nat,
      ~Types.Step,
      ~Ledgers.Line.code.read,
      ~Codes.Code.count.read,
      ~Codes.Code.count.read,
      a => b => c => Types.Step.At{a, b, c},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Types.Step>>,
      U32.is_eq(x, 1),
      u => Some{Codes.Read{Types.Step.Broken{}, r}},
      u => None{}
    )
  )

# a step
def Step.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Step>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Step.code.read.of(x, r)

# a step reads back
def Step.code_read(
  x: Types.Step,
  r: List<&2, U32>
) -> {Step.code.read(Step.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Step>>}:
  match x:
    case Types.Step.At{x0, x1, x2}:
      Codes.Code.three_read(
        ~Ledgers.Line,
        ~Nat,
        ~Nat,
        ~Types.Step,
        ~Ledgers.Line.codec(),
        ~Count.codec(),
        ~Count.codec(),
        a => b => c => Types.Step.At{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Types.Step.Broken{}:
      {==}

# the code of steps
def Step.codec() -> Codes.Codec(Types.Step):
  (Step.code, (Step.code.read, x => r => Step.code_read(x, r)))

# the ballots x of a voter, then r
def Ref.code(x: Types.Ref, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Ref{x0, x1}:
      Codes.Code.text(x0, Codes.Code.count(x1, r))

# the ballots of a voter
def Ref.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Ref>>:
  Codes.Code.two.read(
    ~String,
    ~Nat,
    ~Types.Ref,
    ~Codes.Code.text.read,
    ~Codes.Code.count.read,
    a => b => Types.Ref{a, b},
    ts
  )

# the ballots of a voter read back
def Ref.code_read(
  x: Types.Ref,
  r: List<&2, U32>
) -> {Ref.code.read(Ref.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Ref>>}:
  match x:
    case Types.Ref{x0, x1}:
      Codes.Code.two_read(
        ~String,
        ~Nat,
        ~Types.Ref,
        ~Codes.Code.text.codec(),
        ~Count.codec(),
        a => b => Types.Ref{a, b},
        x0,
        x1,
        r
      )

# the code of the ballots of a voter
def Ref.codec() -> Codes.Codec(Types.Ref):
  (Ref.code, (Ref.code.read, x => r => Ref.code_read(x, r)))

# the basis x, then r
def Refs.code(x: List<&2, Types.Ref>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Types.Ref, ~Ref.code, x, r)

# a basis
def Refs.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Types.Ref>>>:
  Codes.Code.list.read(~Types.Ref, ~Ref.code.read, ts)

# the code of a basis
def Refs.codec() -> Codes.Codec(List<&2, Types.Ref>):
  Codes.Code.list.codec(~Types.Ref, ~Ref.codec())

# the cast x, then r
def Cast.code(x: Types.Cast, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Cast.Vote{x0, x1, x2}:
      0 <> Codes.Code.count(x0, Pick.code(x1, Refs.code(x2, r)))
    case Types.Cast.Pass{x0}:
      1 <> Codes.Code.count(x0, r)

# a cast whose tag is x, from the tokens r after it
def Cast.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Cast>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Types.Cast>>,
    U32.is_eq(x, 0),
    u => Codes.Code.three.read(
      ~Nat,
      ~Types.Pick,
      ~List<&2, Types.Ref>,
      ~Types.Cast,
      ~Codes.Code.count.read,
      ~Pick.code.read,
      ~Refs.code.read,
      a => b => c => Types.Cast.Vote{a, b, c},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Types.Cast>>,
      U32.is_eq(x, 1),
      u => Codes.Code.one.read(
        ~Nat,
        ~Types.Cast,
        ~Codes.Code.count.read,
        a => Types.Cast.Pass{a},
        r
      ),
      u => None{}
    )
  )

# a cast
def Cast.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Cast>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Cast.code.read.of(x, r)

# a cast reads back
def Cast.code_read(
  x: Types.Cast,
  r: List<&2, U32>
) -> {Cast.code.read(Cast.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Cast>>}:
  match x:
    case Types.Cast.Vote{x0, x1, x2}:
      Codes.Code.three_read(
        ~Nat,
        ~Types.Pick,
        ~List<&2, Types.Ref>,
        ~Types.Cast,
        ~Count.codec(),
        ~Pick.codec(),
        ~Refs.codec(),
        a => b => c => Types.Cast.Vote{a, b, c},
        x0,
        x1,
        x2,
        r
      )
    case Types.Cast.Pass{x0}:
      Codes.Code.one_read(~Nat, ~Types.Cast, ~Count.codec(), a => Types.Cast.Pass{a}, x0, r)

# the code of casts
def Cast.codec() -> Codes.Codec(Types.Cast):
  (Cast.code, (Cast.code.read, x => r => Cast.code_read(x, r)))

# the fact x, then r
def Fact.code(x: Types.Fact, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Types.Fact.Ask{x0}:
      0 <> Ask.code(x0, r)
    case Types.Fact.Vote{x0, x1, x2}:
      1 <> Codes.Code.text(x0, Step.code(x1, Cast.code(x2, r)))

# a fact whose tag is x, from the tokens r after it
def Fact.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Fact>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Types.Fact>>,
    U32.is_eq(x, 0),
    u => Codes.Code.one.read(~Types.Ask, ~Types.Fact, ~Ask.code.read, a => Types.Fact.Ask{a}, r),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Types.Fact>>,
      U32.is_eq(x, 1),
      u => Codes.Code.three.read(
        ~String,
        ~Types.Step,
        ~Types.Cast,
        ~Types.Fact,
        ~Codes.Code.text.read,
        ~Step.code.read,
        ~Cast.code.read,
        a => b => c => Types.Fact.Vote{a, b, c},
        r
      ),
      u => None{}
    )
  )

# a fact
def Fact.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Fact.code.read.of(x, r)

# a fact reads back
def Fact.code_read(
  x: Types.Fact,
  r: List<&2, U32>
) -> {Fact.code.read(Fact.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Types.Fact>>}:
  match x:
    case Types.Fact.Ask{x0}:
      Codes.Code.one_read(~Types.Ask, ~Types.Fact, ~Ask.codec(), a => Types.Fact.Ask{a}, x0, r)
    case Types.Fact.Vote{x0, x1, x2}:
      Codes.Code.three_read(
        ~String,
        ~Types.Step,
        ~Types.Cast,
        ~Types.Fact,
        ~Codes.Code.text.codec(),
        ~Step.codec(),
        ~Cast.codec(),
        a => b => c => Types.Fact.Vote{a, b, c},
        x0,
        x1,
        x2,
        r
      )

# the code of facts
def Fact.codec() -> Codes.Codec(Types.Fact):
  (Fact.code, (Fact.code.read, x => r => Fact.code_read(x, r)))

# Equalities
# ----------
# Two values are compared part by part, with no code; X.is_eq_code says
# that this is what the codes give.

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the sides are the parts of one value: where it costs (Rounds.Slot.decided) the two values are equal, so every part is read anyway; Cast.is_eq of a vote and itself takes 12k instructions, by its code 105k (callgrind, tools/drivers/main9.bend); in the laws a proof does not run
# the words of the request x: its code
def Request.words(x: Spec.Request) -> List<&2, U32>:
  Request.code(x, [])

# a and b are the same words, or both none
def Content.is_eq(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x0} Some{y0}:
      Crits.Key.is_eq(x0, y0)
    case _ _:
      False{}

# Content.is_eq is True for words, if any, and themselves
def Content.is_eq_refl(a: Maybe<&2, List<&2, U32>>) -> {Content.is_eq(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{+x0}:
      Crits.Key.is_eq_refl(x0)

# Content.is_eq is True only for equal words, if any
def Content.is_eq_sound(
  a: Maybe<&2, List<&2, U32>>,
  b: Maybe<&2, List<&2, U32>>
) -> {Content.is_eq(a, b) == True{}: Bool} -> {a == b: Maybe<&2, List<&2, U32>>}:
  match a b:
    case None{} None{}:
      h => {==}
    case None{} Some{y0}:
      h => Empty.absurd(
        {None{} == Some{y0}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{x0} None{}:
      h => Empty.absurd(
        {Some{x0} == None{}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{+x0} Some{+y0}:
      +h =>
        %Crits.Key.is_eq_sound(x0, y0)(h): {Some{x0} == Some{_}: Maybe<&2, List<&2, U32>>}
        {==}

# the laws of Content.is_eq
def Content.laws() -> Shared.Eq.Laws(Maybe<&2, List<&2, U32>>, Content.is_eq):
  (x => Content.is_eq_refl(x), x => y => Content.is_eq_sound(x, y))

# a and b are the same texts
def Texts.is_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x0, x1} Con{y0, y1}:
      Bool.and(String.eq(x0, y0), Texts.is_eq(x1, y1))
    case _ _:
      False{}

# Texts.is_eq is True for texts and themselves
def Texts.is_eq_refl(a: List<&2, String>) -> {Texts.is_eq(a, a) == True{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x0, +x1}:
      Shared.Bool.and_both(
        String.eq(x0, x0),
        Texts.is_eq(x1, x1)
      )(Strings.String.eq_refl(x0))(Texts.is_eq_refl(x1))

# Texts.is_eq is True only for equal texts
def Texts.is_eq_sound(
  a: List<&2, String>,
  b: List<&2, String>
) -> {Texts.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, String>}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y0, y1}:
      h => Empty.absurd({Nil{} == Con{y0, y1}: List<&2, String>}, Shared.Bool.false_ne_true(h))
    case Con{x0, x1} Nil{}:
      h => Empty.absurd({Con{x0, x1} == Nil{}: List<&2, String>}, Shared.Bool.false_ne_true(h))
    case Con{+x0, +x1} Con{+y0, +y1}:
      +h =>
        %Strings.String.eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(String.eq(x0, y0), Texts.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{_, y1}: List<&2, String>}
        %Texts.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(String.eq(x0, y0), Texts.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{x0, _}: List<&2, String>}
        {==}

# the laws of Texts.is_eq
def Texts.laws() -> Shared.Eq.Laws(List<&2, String>, Texts.is_eq):
  (x => Texts.is_eq_refl(x), x => y => Texts.is_eq_sound(x, y))

# a and b are the same request
def Request.is_eq(a: Spec.Request, b: Spec.Request) -> Bool:
  match a b:
    case Spec.Request.Start{x0} Spec.Request.Start{y0}:
      Texts.is_eq(x0, y0)
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Write{y0, y1, y2}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2)))
    case Spec.Request.Merge{x0, x1} Spec.Request.Merge{y0, y1}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Ledgers.Line.is_eq(x1, y1))
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Resolve{y0, y1, y2}:
      Bool.and(Ledgers.Id.is_eq(x0, y0), Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2)))
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Mark{y0, y1, y2}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Bool.and(String.eq(x1, y1), Nat.is_eq(x2, y2)))
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Move{y0, y1, y2}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Bool.and(Ledgers.Line.is_eq(x1, y1), Nat.is_eq(x2, y2)))
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Group{y0, y1, y2}:
      Bool.and(Hashes.Hash.is_eq(x0, y0), Bool.and(String.eq(x1, y1), Texts.is_eq(x2, y2)))
    case Spec.Request.Own{x0, x1} Spec.Request.Own{y0, y1}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), String.eq(x1, y1))
    case _ _:
      False{}

# Request.is_eq is True for a request and itself
def Request.is_eq_refl(a: Spec.Request) -> {Request.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Request.Start{+x0}:
      Texts.is_eq_refl(x0)
    case Spec.Request.Write{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Bool.and(String.eq(x1, x1), Content.is_eq(x2, x2))
      )(
        Ledgers.Line.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          String.eq(x1, x1),
          Content.is_eq(x2, x2)
        )(Strings.String.eq_refl(x1))(Content.is_eq_refl(x2))
      )
    case Spec.Request.Merge{+x0, +x1}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Ledgers.Line.is_eq(x1, x1)
      )(Ledgers.Line.is_eq_refl(x0))(Ledgers.Line.is_eq_refl(x1))
    case Spec.Request.Resolve{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Id.is_eq(x0, x0),
        Bool.and(String.eq(x1, x1), Content.is_eq(x2, x2))
      )(
        Ledgers.Id.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          String.eq(x1, x1),
          Content.is_eq(x2, x2)
        )(Strings.String.eq_refl(x1))(Content.is_eq_refl(x2))
      )
    case Spec.Request.Mark{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Bool.and(String.eq(x1, x1), Nat.is_eq(x2, x2))
      )(
        Ledgers.Line.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          String.eq(x1, x1),
          Nat.is_eq(x2, x2)
        )(Strings.String.eq_refl(x1))(Shared.Nat.is_eq_refl(x2))
      )
    case Spec.Request.Move{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Bool.and(Ledgers.Line.is_eq(x1, x1), Nat.is_eq(x2, x2))
      )(
        Ledgers.Line.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Ledgers.Line.is_eq(x1, x1),
          Nat.is_eq(x2, x2)
        )(Ledgers.Line.is_eq_refl(x1))(Shared.Nat.is_eq_refl(x2))
      )
    case Spec.Request.Group{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Hashes.Hash.is_eq(x0, x0),
        Bool.and(String.eq(x1, x1), Texts.is_eq(x2, x2))
      )(
        Hashes.Hash.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          String.eq(x1, x1),
          Texts.is_eq(x2, x2)
        )(Strings.String.eq_refl(x1))(Texts.is_eq_refl(x2))
      )
    case Spec.Request.Own{+x0, +x1}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        String.eq(x1, x1)
      )(Ledgers.Line.is_eq_refl(x0))(Strings.String.eq_refl(x1))

# Request.is_eq is True only for equal requests
def Request.is_eq_sound(
  a: Spec.Request,
  b: Spec.Request
) -> {Request.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Request}:
  match a b:
    case Spec.Request.Start{+x0} Spec.Request.Start{+y0}:
      +h =>
        %Texts.is_eq_sound(
          x0,
          y0
        )(h): {Spec.Request.Start{x0} == Spec.Request.Start{_}: Spec.Request}
        {==}
    case Spec.Request.Start{x0} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Start{x0} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Start{x0} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{+x0, +x1, +x2} Spec.Request.Write{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Line.is_eq(x0, y0),
            Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
          )(h)
        ): {Spec.Request.Write{x0, x1, x2} == Spec.Request.Write{_, y1, y2}: Spec.Request}
        %Strings.String.eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            String.eq(x1, y1),
            Content.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Write{x0, x1, x2} == Spec.Request.Write{x0, _, y2}: Spec.Request}
        %Content.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            String.eq(x1, y1),
            Content.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Write{x0, x1, x2} == Spec.Request.Write{x0, x1, _}: Spec.Request}
        {==}
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{x0, x1, x2} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Write{x0, x1, x2} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{+x0, +x1} Spec.Request.Merge{+y0, +y1}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Ledgers.Line.is_eq(x0, y0), Ledgers.Line.is_eq(x1, y1))(h)
        ): {Spec.Request.Merge{x0, x1} == Spec.Request.Merge{_, y1}: Spec.Request}
        %Ledgers.Line.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Ledgers.Line.is_eq(x0, y0), Ledgers.Line.is_eq(x1, y1))(h)
        ): {Spec.Request.Merge{x0, x1} == Spec.Request.Merge{x0, _}: Spec.Request}
        {==}
    case Spec.Request.Merge{x0, x1} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{x0, x1} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Merge{x0, x1} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{+x0, +x1, +x2} Spec.Request.Resolve{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Id.is_eq(x0, y0),
            Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
          )(h)
        ): {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Resolve{_, y1, y2}: Spec.Request}
        %Strings.String.eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            String.eq(x1, y1),
            Content.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Id.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Resolve{x0, _, y2}: Spec.Request}
        %Content.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            String.eq(x1, y1),
            Content.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Id.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Content.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Resolve{x0, x1, _}: Spec.Request}
        {==}
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{x0, x1, x2} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Resolve{x0, x1, x2} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{+x0, +x1, +x2} Spec.Request.Mark{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Line.is_eq(x0, y0),
            Bool.and(String.eq(x1, y1), Nat.is_eq(x2, y2))
          )(h)
        ): {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Mark{_, y1, y2}: Spec.Request}
        %Strings.String.eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            String.eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Mark{x0, _, y2}: Spec.Request}
        %Shared.Nat.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            String.eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Mark{x0, x1, _}: Spec.Request}
        {==}
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{x0, x1, x2} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Mark{x0, x1, x2} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{+x0, +x1, +x2} Spec.Request.Move{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Line.is_eq(x0, y0),
            Bool.and(Ledgers.Line.is_eq(x1, y1), Nat.is_eq(x2, y2))
          )(h)
        ): {Spec.Request.Move{x0, x1, x2} == Spec.Request.Move{_, y1, y2}: Spec.Request}
        %Ledgers.Line.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Ledgers.Line.is_eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(Ledgers.Line.is_eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Move{x0, x1, x2} == Spec.Request.Move{x0, _, y2}: Spec.Request}
        %Shared.Nat.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            Ledgers.Line.is_eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(Ledgers.Line.is_eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Move{x0, x1, x2} == Spec.Request.Move{x0, x1, _}: Spec.Request}
        {==}
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{x0, x1, x2} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Move{x0, x1, x2} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{+x0, +x1, +x2} Spec.Request.Group{+y0, +y1, +y2}:
      +h =>
        %Hashes.Hash.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Hashes.Hash.is_eq(x0, y0),
            Bool.and(String.eq(x1, y1), Texts.is_eq(x2, y2))
          )(h)
        ): {Spec.Request.Group{x0, x1, x2} == Spec.Request.Group{_, y1, y2}: Spec.Request}
        %Strings.String.eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            String.eq(x1, y1),
            Texts.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Hashes.Hash.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Texts.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Group{x0, x1, x2} == Spec.Request.Group{x0, _, y2}: Spec.Request}
        %Texts.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            String.eq(x1, y1),
            Texts.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Hashes.Hash.is_eq(x0, y0),
              Bool.and(String.eq(x1, y1), Texts.is_eq(x2, y2))
            )(h)
          )
        ): {Spec.Request.Group{x0, x1, x2} == Spec.Request.Group{x0, x1, _}: Spec.Request}
        {==}
    case Spec.Request.Group{x0, x1, x2} Spec.Request.Own{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Group{x0, x1, x2} == Spec.Request.Own{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Start{y0}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Start{y0}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Write{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Write{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Merge{y0, y1}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Merge{y0, y1}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Resolve{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Resolve{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Mark{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Mark{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Move{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Move{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{x0, x1} Spec.Request.Group{y0, y1, y2}:
      h => Empty.absurd(
        {Spec.Request.Own{x0, x1} == Spec.Request.Group{y0, y1, y2}: Spec.Request},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{+x0, +x1} Spec.Request.Own{+y0, +y1}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Ledgers.Line.is_eq(x0, y0), String.eq(x1, y1))(h)
        ): {Spec.Request.Own{x0, x1} == Spec.Request.Own{_, y1}: Spec.Request}
        %Strings.String.eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Ledgers.Line.is_eq(x0, y0), String.eq(x1, y1))(h)
        ): {Spec.Request.Own{x0, x1} == Spec.Request.Own{x0, _}: Spec.Request}
        {==}

# the laws of Request.is_eq
def Request.laws() -> Shared.Eq.Laws(Spec.Request, Request.is_eq):
  (x => Request.is_eq_refl(x), x => y => Request.is_eq_sound(x, y))

# Request.is_eq gives what the codes give: two requests are the same when
# their words are
def Request.is_eq_code(
  +a: Spec.Request,
  +b: Spec.Request
) -> {Request.is_eq(a, b) == Codes.Code.is_eq(~Spec.Request, ~Request.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Spec.Request,
    ~Request.is_eq,
    ~(x => y => Codes.Code.is_eq(~Spec.Request, ~Request.code, x, y)),
    ~Request.laws(),
    ~Codes.Code.eq_laws(~Spec.Request, ~Request.codec()),
    a,
    b
  )

# the words of the ask x: its code
def Ask.words(x: Types.Ask) -> List<&2, U32>:
  Ask.code(x, [])

# a and b are the same ask
def Ask.is_eq(a: Types.Ask, b: Types.Ask) -> Bool:
  match a b:
    case Types.Ask{x0, x1, x2} Types.Ask{y0, y1, y2}:
      Bool.and(Ledgers.Id.is_eq(x0, y0), Bool.and(Nat.is_eq(x1, y1), Request.is_eq(x2, y2)))

# Ask.is_eq is True for an ask and itself
def Ask.is_eq_refl(a: Types.Ask) -> {Ask.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Ask{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Id.is_eq(x0, x0),
        Bool.and(Nat.is_eq(x1, x1), Request.is_eq(x2, x2))
      )(
        Ledgers.Id.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(x1, x1),
          Request.is_eq(x2, x2)
        )(Shared.Nat.is_eq_refl(x1))(Request.is_eq_refl(x2))
      )

# Ask.is_eq is True only for equal asks
def Ask.is_eq_sound(
  a: Types.Ask,
  b: Types.Ask
) -> {Ask.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Ask}:
  match a b:
    case Types.Ask{+x0, +x1, +x2} Types.Ask{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Id.is_eq(x0, y0),
            Bool.and(Nat.is_eq(x1, y1), Request.is_eq(x2, y2))
          )(h)
        ): {Types.Ask{x0, x1, x2} == Types.Ask{_, y1, y2}: Types.Ask}
        %Shared.Nat.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Nat.is_eq(x1, y1),
            Request.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Id.is_eq(x0, y0),
              Bool.and(Nat.is_eq(x1, y1), Request.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Ask{x0, x1, x2} == Types.Ask{x0, _, y2}: Types.Ask}
        %Request.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            Nat.is_eq(x1, y1),
            Request.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Id.is_eq(x0, y0),
              Bool.and(Nat.is_eq(x1, y1), Request.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Ask{x0, x1, x2} == Types.Ask{x0, x1, _}: Types.Ask}
        {==}

# the laws of Ask.is_eq
def Ask.laws() -> Shared.Eq.Laws(Types.Ask, Ask.is_eq):
  (x => Ask.is_eq_refl(x), x => y => Ask.is_eq_sound(x, y))

# Ask.is_eq gives what the codes give: two asks are the same when
# their words are
def Ask.is_eq_code(
  +a: Types.Ask,
  +b: Types.Ask
) -> {Ask.is_eq(a, b) == Codes.Code.is_eq(~Types.Ask, ~Ask.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Types.Ask,
    ~Ask.is_eq,
    ~(x => y => Codes.Code.is_eq(~Types.Ask, ~Ask.code, x, y)),
    ~Ask.laws(),
    ~Codes.Code.eq_laws(~Types.Ask, ~Ask.codec()),
    a,
    b
  )

# the words of the pick x: its code
def Pick.words(x: Types.Pick) -> List<&2, U32>:
  Pick.code(x, [])

# a and b are the same version
def Point.is_eq(a: Spec.Point, b: Spec.Point) -> Bool:
  match a b:
    case Spec.Point{x0, x1} Spec.Point{y0, y1}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Nat.is_eq(x1, y1))

# Point.is_eq is True for a version and itself
def Point.is_eq_refl(a: Spec.Point) -> {Point.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Point{+x0, +x1}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Nat.is_eq(x1, x1)
      )(Ledgers.Line.is_eq_refl(x0))(Shared.Nat.is_eq_refl(x1))

# Point.is_eq is True only for equal versions
def Point.is_eq_sound(
  a: Spec.Point,
  b: Spec.Point
) -> {Point.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Point}:
  match a b:
    case Spec.Point{+x0, +x1} Spec.Point{+y0, +y1}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Ledgers.Line.is_eq(x0, y0), Nat.is_eq(x1, y1))(h)
        ): {Spec.Point{x0, x1} == Spec.Point{_, y1}: Spec.Point}
        %Shared.Nat.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Ledgers.Line.is_eq(x0, y0), Nat.is_eq(x1, y1))(h)
        ): {Spec.Point{x0, x1} == Spec.Point{x0, _}: Spec.Point}
        {==}

# the laws of Point.is_eq
def Point.laws() -> Shared.Eq.Laws(Spec.Point, Point.is_eq):
  (x => Point.is_eq_refl(x), x => y => Point.is_eq_sound(x, y))

# a and b are the same version, or both none
def Base.is_eq(a: Maybe<&2, Spec.Point>, b: Maybe<&2, Spec.Point>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x0} Some{y0}:
      Point.is_eq(x0, y0)
    case _ _:
      False{}

# Base.is_eq is True for a version, if any, and itself
def Base.is_eq_refl(a: Maybe<&2, Spec.Point>) -> {Base.is_eq(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{+x0}:
      Point.is_eq_refl(x0)

# Base.is_eq is True only for equal versions, if any
def Base.is_eq_sound(
  a: Maybe<&2, Spec.Point>,
  b: Maybe<&2, Spec.Point>
) -> {Base.is_eq(a, b) == True{}: Bool} -> {a == b: Maybe<&2, Spec.Point>}:
  match a b:
    case None{} None{}:
      h => {==}
    case None{} Some{y0}:
      h => Empty.absurd({None{} == Some{y0}: Maybe<&2, Spec.Point>}, Shared.Bool.false_ne_true(h))
    case Some{x0} None{}:
      h => Empty.absurd({Some{x0} == None{}: Maybe<&2, Spec.Point>}, Shared.Bool.false_ne_true(h))
    case Some{+x0} Some{+y0}:
      +h =>
        %Point.is_eq_sound(x0, y0)(h): {Some{x0} == Some{_}: Maybe<&2, Spec.Point>}
        {==}

# the laws of Base.is_eq
def Base.laws() -> Shared.Eq.Laws(Maybe<&2, Spec.Point>, Base.is_eq):
  (x => Base.is_eq_refl(x), x => y => Base.is_eq_sound(x, y))

# a and b are the same versions
def Points.is_eq(a: List<&2, Spec.Point>, b: List<&2, Spec.Point>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x0, x1} Con{y0, y1}:
      Bool.and(Point.is_eq(x0, y0), Points.is_eq(x1, y1))
    case _ _:
      False{}

# Points.is_eq is True for versions and themselves
def Points.is_eq_refl(a: List<&2, Spec.Point>) -> {Points.is_eq(a, a) == True{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x0, +x1}:
      Shared.Bool.and_both(
        Point.is_eq(x0, x0),
        Points.is_eq(x1, x1)
      )(Point.is_eq_refl(x0))(Points.is_eq_refl(x1))

# Points.is_eq is True only for equal versions
def Points.is_eq_sound(
  a: List<&2, Spec.Point>,
  b: List<&2, Spec.Point>
) -> {Points.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, Spec.Point>}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y0, y1}:
      h => Empty.absurd({Nil{} == Con{y0, y1}: List<&2, Spec.Point>}, Shared.Bool.false_ne_true(h))
    case Con{x0, x1} Nil{}:
      h => Empty.absurd({Con{x0, x1} == Nil{}: List<&2, Spec.Point>}, Shared.Bool.false_ne_true(h))
    case Con{+x0, +x1} Con{+y0, +y1}:
      +h =>
        %Point.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Point.is_eq(x0, y0), Points.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{_, y1}: List<&2, Spec.Point>}
        %Points.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Point.is_eq(x0, y0), Points.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{x0, _}: List<&2, Spec.Point>}
        {==}

# the laws of Points.is_eq
def Points.laws() -> Shared.Eq.Laws(List<&2, Spec.Point>, Points.is_eq):
  (x => Points.is_eq_refl(x), x => y => Points.is_eq_sound(x, y))

# a and b are the same pins
def Pins.is_eq(a: Types.Pins, b: Types.Pins) -> Bool:
  match a b:
    case Types.Pins{x0, x1, x2, x3, x4} Types.Pins{y0, y1, y2, y3, y4}:
      Bool.and(
        Nat.is_eq(x0, y0),
        Bool.and(
          Nat.is_eq(x1, y1),
          Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
        )
      )

# Pins.is_eq is True for pins and themselves
def Pins.is_eq_refl(a: Types.Pins) -> {Pins.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Pins{+x0, +x1, +x2, +x3, +x4}:
      Shared.Bool.and_both(
        Nat.is_eq(x0, x0),
        Bool.and(
          Nat.is_eq(x1, x1),
          Bool.and(Base.is_eq(x2, x2), Bool.and(Points.is_eq(x3, x3), Points.is_eq(x4, x4)))
        )
      )(
        Shared.Nat.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(x1, x1),
          Bool.and(Base.is_eq(x2, x2), Bool.and(Points.is_eq(x3, x3), Points.is_eq(x4, x4)))
        )(
          Shared.Nat.is_eq_refl(x1)
        )(
          Shared.Bool.and_both(
            Base.is_eq(x2, x2),
            Bool.and(Points.is_eq(x3, x3), Points.is_eq(x4, x4))
          )(
            Base.is_eq_refl(x2)
          )(
            Shared.Bool.and_both(
              Points.is_eq(x3, x3),
              Points.is_eq(x4, x4)
            )(Points.is_eq_refl(x3))(Points.is_eq_refl(x4))
          )
        )
      )

# Pins.is_eq is True only for equal pins
def Pins.is_eq_sound(
  a: Types.Pins,
  b: Types.Pins
) -> {Pins.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Pins}:
  match a b:
    case Types.Pins{+x0, +x1, +x2, +x3, +x4} Types.Pins{+y0, +y1, +y2, +y3, +y4}:
      +h =>
        %Shared.Nat.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Nat.is_eq(x0, y0),
            Bool.and(
              Nat.is_eq(x1, y1),
              Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
            )
          )(h)
        ): {Types.Pins{x0, x1, x2, x3, x4} == Types.Pins{_, y1, y2, y3, y4}: Types.Pins}
        %Shared.Nat.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Nat.is_eq(x1, y1),
            Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
          )(
            Shared.Bool.and_true_right(
              Nat.is_eq(x0, y0),
              Bool.and(
                Nat.is_eq(x1, y1),
                Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
              )
            )(h)
          )
        ): {Types.Pins{x0, x1, x2, x3, x4} == Types.Pins{x0, _, y2, y3, y4}: Types.Pins}
        %Base.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_left(
            Base.is_eq(x2, y2),
            Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4))
          )(
            Shared.Bool.and_true_right(
              Nat.is_eq(x1, y1),
              Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
            )(
              Shared.Bool.and_true_right(
                Nat.is_eq(x0, y0),
                Bool.and(
                  Nat.is_eq(x1, y1),
                  Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
                )
              )(h)
            )
          )
        ): {Types.Pins{x0, x1, x2, x3, x4} == Types.Pins{x0, x1, _, y3, y4}: Types.Pins}
        %Points.is_eq_sound(
          x3,
          y3
        )(
          Shared.Bool.and_true_left(
            Points.is_eq(x3, y3),
            Points.is_eq(x4, y4)
          )(
            Shared.Bool.and_true_right(
              Base.is_eq(x2, y2),
              Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4))
            )(
              Shared.Bool.and_true_right(
                Nat.is_eq(x1, y1),
                Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
              )(
                Shared.Bool.and_true_right(
                  Nat.is_eq(x0, y0),
                  Bool.and(
                    Nat.is_eq(x1, y1),
                    Bool.and(
                      Base.is_eq(x2, y2),
                      Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4))
                    )
                  )
                )(h)
              )
            )
          )
        ): {Types.Pins{x0, x1, x2, x3, x4} == Types.Pins{x0, x1, x2, _, y4}: Types.Pins}
        %Points.is_eq_sound(
          x4,
          y4
        )(
          Shared.Bool.and_true_right(
            Points.is_eq(x3, y3),
            Points.is_eq(x4, y4)
          )(
            Shared.Bool.and_true_right(
              Base.is_eq(x2, y2),
              Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4))
            )(
              Shared.Bool.and_true_right(
                Nat.is_eq(x1, y1),
                Bool.and(Base.is_eq(x2, y2), Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4)))
              )(
                Shared.Bool.and_true_right(
                  Nat.is_eq(x0, y0),
                  Bool.and(
                    Nat.is_eq(x1, y1),
                    Bool.and(
                      Base.is_eq(x2, y2),
                      Bool.and(Points.is_eq(x3, y3), Points.is_eq(x4, y4))
                    )
                  )
                )(h)
              )
            )
          )
        ): {Types.Pins{x0, x1, x2, x3, x4} == Types.Pins{x0, x1, x2, x3, _}: Types.Pins}
        {==}

# the laws of Pins.is_eq
def Pins.laws() -> Shared.Eq.Laws(Types.Pins, Pins.is_eq):
  (x => Pins.is_eq_refl(x), x => y => Pins.is_eq_sound(x, y))

# a and b are the same pick
def Pick.is_eq(a: Types.Pick, b: Types.Pick) -> Bool:
  match a b:
    case Types.Pick{x0, x1} Types.Pick{y0, y1}:
      Bool.and(Ask.is_eq(x0, y0), Pins.is_eq(x1, y1))

# Pick.is_eq is True for a pick and itself
def Pick.is_eq_refl(a: Types.Pick) -> {Pick.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Pick{+x0, +x1}:
      Shared.Bool.and_both(
        Ask.is_eq(x0, x0),
        Pins.is_eq(x1, x1)
      )(Ask.is_eq_refl(x0))(Pins.is_eq_refl(x1))

# Pick.is_eq is True only for equal picks
def Pick.is_eq_sound(
  a: Types.Pick,
  b: Types.Pick
) -> {Pick.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Pick}:
  match a b:
    case Types.Pick{+x0, +x1} Types.Pick{+y0, +y1}:
      +h =>
        %Ask.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Ask.is_eq(x0, y0), Pins.is_eq(x1, y1))(h)
        ): {Types.Pick{x0, x1} == Types.Pick{_, y1}: Types.Pick}
        %Pins.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Ask.is_eq(x0, y0), Pins.is_eq(x1, y1))(h)
        ): {Types.Pick{x0, x1} == Types.Pick{x0, _}: Types.Pick}
        {==}

# the laws of Pick.is_eq
def Pick.laws() -> Shared.Eq.Laws(Types.Pick, Pick.is_eq):
  (x => Pick.is_eq_refl(x), x => y => Pick.is_eq_sound(x, y))

# Pick.is_eq gives what the codes give: two picks are the same when
# their words are
def Pick.is_eq_code(
  +a: Types.Pick,
  +b: Types.Pick
) -> {Pick.is_eq(a, b) == Codes.Code.is_eq(~Types.Pick, ~Pick.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Types.Pick,
    ~Pick.is_eq,
    ~(x => y => Codes.Code.is_eq(~Types.Pick, ~Pick.code, x, y)),
    ~Pick.laws(),
    ~Codes.Code.eq_laws(~Types.Pick, ~Pick.codec()),
    a,
    b
  )

# two picks with the same words are the same
def Pick.words_inj(
  +a: Types.Pick,
  +b: Types.Pick
) -> {Pick.words(a) == Pick.words(b): List<&2, U32>} -> {a == b: Types.Pick}:
  Ledgers.Book.code_value(~Types.Pick, ~Pick.codec(), a, b, [], [])

# the words of the step x: its code
def Step.words(x: Types.Step) -> List<&2, U32>:
  Step.code(x, [])

# a and b are the same step
def Step.is_eq(a: Types.Step, b: Types.Step) -> Bool:
  match a b:
    case Types.Step.At{x0, x1, x2} Types.Step.At{y0, y1, y2}:
      Bool.and(Ledgers.Line.is_eq(x0, y0), Bool.and(Nat.is_eq(x1, y1), Nat.is_eq(x2, y2)))
    case Types.Step.Broken{} Types.Step.Broken{}:
      True{}
    case _ _:
      False{}

# Step.is_eq is True for a step and itself
def Step.is_eq_refl(a: Types.Step) -> {Step.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Step.At{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Line.is_eq(x0, x0),
        Bool.and(Nat.is_eq(x1, x1), Nat.is_eq(x2, x2))
      )(
        Ledgers.Line.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(x1, x1),
          Nat.is_eq(x2, x2)
        )(Shared.Nat.is_eq_refl(x1))(Shared.Nat.is_eq_refl(x2))
      )
    case Types.Step.Broken{}:
      {==}

# Step.is_eq is True only for equal steps
def Step.is_eq_sound(
  a: Types.Step,
  b: Types.Step
) -> {Step.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Step}:
  match a b:
    case Types.Step.At{+x0, +x1, +x2} Types.Step.At{+y0, +y1, +y2}:
      +h =>
        %Ledgers.Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Line.is_eq(x0, y0),
            Bool.and(Nat.is_eq(x1, y1), Nat.is_eq(x2, y2))
          )(h)
        ): {Types.Step.At{x0, x1, x2} == Types.Step.At{_, y1, y2}: Types.Step}
        %Shared.Nat.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Nat.is_eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(Nat.is_eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Step.At{x0, x1, x2} == Types.Step.At{x0, _, y2}: Types.Step}
        %Shared.Nat.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            Nat.is_eq(x1, y1),
            Nat.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Ledgers.Line.is_eq(x0, y0),
              Bool.and(Nat.is_eq(x1, y1), Nat.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Step.At{x0, x1, x2} == Types.Step.At{x0, x1, _}: Types.Step}
        {==}
    case Types.Step.At{x0, x1, x2} Types.Step.Broken{}:
      h => Empty.absurd(
        {Types.Step.At{x0, x1, x2} == Types.Step.Broken{}: Types.Step},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Step.Broken{} Types.Step.At{y0, y1, y2}:
      h => Empty.absurd(
        {Types.Step.Broken{} == Types.Step.At{y0, y1, y2}: Types.Step},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Step.Broken{} Types.Step.Broken{}:
      h => {==}

# the laws of Step.is_eq
def Step.laws() -> Shared.Eq.Laws(Types.Step, Step.is_eq):
  (x => Step.is_eq_refl(x), x => y => Step.is_eq_sound(x, y))

# Step.is_eq gives what the codes give: two steps are the same when
# their words are
def Step.is_eq_code(
  +a: Types.Step,
  +b: Types.Step
) -> {Step.is_eq(a, b) == Codes.Code.is_eq(~Types.Step, ~Step.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Types.Step,
    ~Step.is_eq,
    ~(x => y => Codes.Code.is_eq(~Types.Step, ~Step.code, x, y)),
    ~Step.laws(),
    ~Codes.Code.eq_laws(~Types.Step, ~Step.codec()),
    a,
    b
  )

# two steps with the same words are the same
def Step.words_inj(
  +a: Types.Step,
  +b: Types.Step
) -> {Step.words(a) == Step.words(b): List<&2, U32>} -> {a == b: Types.Step}:
  Ledgers.Book.code_value(~Types.Step, ~Step.codec(), a, b, [], [])

# the words of the cast x: its code
def Cast.words(x: Types.Cast) -> List<&2, U32>:
  Cast.code(x, [])

# a and b are the same reference
def Ref.is_eq(a: Types.Ref, b: Types.Ref) -> Bool:
  match a b:
    case Types.Ref{x0, x1} Types.Ref{y0, y1}:
      Bool.and(String.eq(x0, y0), Nat.is_eq(x1, y1))

# Ref.is_eq is True for a reference and itself
def Ref.is_eq_refl(a: Types.Ref) -> {Ref.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Ref{+x0, +x1}:
      Shared.Bool.and_both(
        String.eq(x0, x0),
        Nat.is_eq(x1, x1)
      )(Strings.String.eq_refl(x0))(Shared.Nat.is_eq_refl(x1))

# Ref.is_eq is True only for equal references
def Ref.is_eq_sound(
  a: Types.Ref,
  b: Types.Ref
) -> {Ref.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Ref}:
  match a b:
    case Types.Ref{+x0, +x1} Types.Ref{+y0, +y1}:
      +h =>
        %Strings.String.eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(String.eq(x0, y0), Nat.is_eq(x1, y1))(h)
        ): {Types.Ref{x0, x1} == Types.Ref{_, y1}: Types.Ref}
        %Shared.Nat.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(String.eq(x0, y0), Nat.is_eq(x1, y1))(h)
        ): {Types.Ref{x0, x1} == Types.Ref{x0, _}: Types.Ref}
        {==}

# the laws of Ref.is_eq
def Ref.laws() -> Shared.Eq.Laws(Types.Ref, Ref.is_eq):
  (x => Ref.is_eq_refl(x), x => y => Ref.is_eq_sound(x, y))

# a and b are the same references
def Refs.is_eq(a: List<&2, Types.Ref>, b: List<&2, Types.Ref>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x0, x1} Con{y0, y1}:
      Bool.and(Ref.is_eq(x0, y0), Refs.is_eq(x1, y1))
    case _ _:
      False{}

# Refs.is_eq is True for references and themselves
def Refs.is_eq_refl(a: List<&2, Types.Ref>) -> {Refs.is_eq(a, a) == True{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x0, +x1}:
      Shared.Bool.and_both(
        Ref.is_eq(x0, x0),
        Refs.is_eq(x1, x1)
      )(Ref.is_eq_refl(x0))(Refs.is_eq_refl(x1))

# Refs.is_eq is True only for equal references
def Refs.is_eq_sound(
  a: List<&2, Types.Ref>,
  b: List<&2, Types.Ref>
) -> {Refs.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, Types.Ref>}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y0, y1}:
      h => Empty.absurd({Nil{} == Con{y0, y1}: List<&2, Types.Ref>}, Shared.Bool.false_ne_true(h))
    case Con{x0, x1} Nil{}:
      h => Empty.absurd({Con{x0, x1} == Nil{}: List<&2, Types.Ref>}, Shared.Bool.false_ne_true(h))
    case Con{+x0, +x1} Con{+y0, +y1}:
      +h =>
        %Ref.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(Ref.is_eq(x0, y0), Refs.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{_, y1}: List<&2, Types.Ref>}
        %Refs.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_right(Ref.is_eq(x0, y0), Refs.is_eq(x1, y1))(h)
        ): {Con{x0, x1} == Con{x0, _}: List<&2, Types.Ref>}
        {==}

# the laws of Refs.is_eq
def Refs.laws() -> Shared.Eq.Laws(List<&2, Types.Ref>, Refs.is_eq):
  (x => Refs.is_eq_refl(x), x => y => Refs.is_eq_sound(x, y))

# a and b are the same cast
def Cast.is_eq(a: Types.Cast, b: Types.Cast) -> Bool:
  match a b:
    case Types.Cast.Vote{x0, x1, x2} Types.Cast.Vote{y0, y1, y2}:
      Bool.and(Nat.is_eq(x0, y0), Bool.and(Pick.is_eq(x1, y1), Refs.is_eq(x2, y2)))
    case Types.Cast.Pass{x0} Types.Cast.Pass{y0}:
      Nat.is_eq(x0, y0)
    case _ _:
      False{}

# Cast.is_eq is True for a cast and itself
def Cast.is_eq_refl(a: Types.Cast) -> {Cast.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Cast.Vote{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Nat.is_eq(x0, x0),
        Bool.and(Pick.is_eq(x1, x1), Refs.is_eq(x2, x2))
      )(
        Shared.Nat.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Pick.is_eq(x1, x1),
          Refs.is_eq(x2, x2)
        )(Pick.is_eq_refl(x1))(Refs.is_eq_refl(x2))
      )
    case Types.Cast.Pass{+x0}:
      Shared.Nat.is_eq_refl(x0)

# Cast.is_eq is True only for equal casts
def Cast.is_eq_sound(
  a: Types.Cast,
  b: Types.Cast
) -> {Cast.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Cast}:
  match a b:
    case Types.Cast.Vote{+x0, +x1, +x2} Types.Cast.Vote{+y0, +y1, +y2}:
      +h =>
        %Shared.Nat.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Nat.is_eq(x0, y0),
            Bool.and(Pick.is_eq(x1, y1), Refs.is_eq(x2, y2))
          )(h)
        ): {Types.Cast.Vote{x0, x1, x2} == Types.Cast.Vote{_, y1, y2}: Types.Cast}
        %Pick.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Pick.is_eq(x1, y1),
            Refs.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Nat.is_eq(x0, y0),
              Bool.and(Pick.is_eq(x1, y1), Refs.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Cast.Vote{x0, x1, x2} == Types.Cast.Vote{x0, _, y2}: Types.Cast}
        %Refs.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            Pick.is_eq(x1, y1),
            Refs.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              Nat.is_eq(x0, y0),
              Bool.and(Pick.is_eq(x1, y1), Refs.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Cast.Vote{x0, x1, x2} == Types.Cast.Vote{x0, x1, _}: Types.Cast}
        {==}
    case Types.Cast.Vote{x0, x1, x2} Types.Cast.Pass{y0}:
      h => Empty.absurd(
        {Types.Cast.Vote{x0, x1, x2} == Types.Cast.Pass{y0}: Types.Cast},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Cast.Pass{x0} Types.Cast.Vote{y0, y1, y2}:
      h => Empty.absurd(
        {Types.Cast.Pass{x0} == Types.Cast.Vote{y0, y1, y2}: Types.Cast},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Cast.Pass{+x0} Types.Cast.Pass{+y0}:
      +h =>
        %Shared.Nat.is_eq_sound(x0, y0)(h): {Types.Cast.Pass{x0} == Types.Cast.Pass{_}: Types.Cast}
        {==}

# the laws of Cast.is_eq
def Cast.laws() -> Shared.Eq.Laws(Types.Cast, Cast.is_eq):
  (x => Cast.is_eq_refl(x), x => y => Cast.is_eq_sound(x, y))

# Cast.is_eq gives what the codes give: two casts are the same when
# their words are
def Cast.is_eq_code(
  +a: Types.Cast,
  +b: Types.Cast
) -> {Cast.is_eq(a, b) == Codes.Code.is_eq(~Types.Cast, ~Cast.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Types.Cast,
    ~Cast.is_eq,
    ~(x => y => Codes.Code.is_eq(~Types.Cast, ~Cast.code, x, y)),
    ~Cast.laws(),
    ~Codes.Code.eq_laws(~Types.Cast, ~Cast.codec()),
    a,
    b
  )

# two casts with the same words are the same
def Cast.words_inj(
  +a: Types.Cast,
  +b: Types.Cast
) -> {Cast.words(a) == Cast.words(b): List<&2, U32>} -> {a == b: Types.Cast}:
  Ledgers.Book.code_value(~Types.Cast, ~Cast.codec(), a, b, [], [])

# the words of the fact x: its code
def Fact.words(x: Types.Fact) -> List<&2, U32>:
  Fact.code(x, [])

# a and b are the same fact
def Fact.is_eq(a: Types.Fact, b: Types.Fact) -> Bool:
  match a b:
    case Types.Fact.Ask{x0} Types.Fact.Ask{y0}:
      Ask.is_eq(x0, y0)
    case Types.Fact.Vote{x0, x1, x2} Types.Fact.Vote{y0, y1, y2}:
      Bool.and(String.eq(x0, y0), Bool.and(Step.is_eq(x1, y1), Cast.is_eq(x2, y2)))
    case _ _:
      False{}

# Fact.is_eq is True for a fact and itself
def Fact.is_eq_refl(a: Types.Fact) -> {Fact.is_eq(a, a) == True{}: Bool}:
  match a:
    case Types.Fact.Ask{+x0}:
      Ask.is_eq_refl(x0)
    case Types.Fact.Vote{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        String.eq(x0, x0),
        Bool.and(Step.is_eq(x1, x1), Cast.is_eq(x2, x2))
      )(
        Strings.String.eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Step.is_eq(x1, x1),
          Cast.is_eq(x2, x2)
        )(Step.is_eq_refl(x1))(Cast.is_eq_refl(x2))
      )

# Fact.is_eq is True only for equal facts
def Fact.is_eq_sound(
  a: Types.Fact,
  b: Types.Fact
) -> {Fact.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Fact}:
  match a b:
    case Types.Fact.Ask{+x0} Types.Fact.Ask{+y0}:
      +h =>
        %Ask.is_eq_sound(x0, y0)(h): {Types.Fact.Ask{x0} == Types.Fact.Ask{_}: Types.Fact}
        {==}
    case Types.Fact.Ask{x0} Types.Fact.Vote{y0, y1, y2}:
      h => Empty.absurd(
        {Types.Fact.Ask{x0} == Types.Fact.Vote{y0, y1, y2}: Types.Fact},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Fact.Vote{x0, x1, x2} Types.Fact.Ask{y0}:
      h => Empty.absurd(
        {Types.Fact.Vote{x0, x1, x2} == Types.Fact.Ask{y0}: Types.Fact},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Fact.Vote{+x0, +x1, +x2} Types.Fact.Vote{+y0, +y1, +y2}:
      +h =>
        %Strings.String.eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            String.eq(x0, y0),
            Bool.and(Step.is_eq(x1, y1), Cast.is_eq(x2, y2))
          )(h)
        ): {Types.Fact.Vote{x0, x1, x2} == Types.Fact.Vote{_, y1, y2}: Types.Fact}
        %Step.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Step.is_eq(x1, y1),
            Cast.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              String.eq(x0, y0),
              Bool.and(Step.is_eq(x1, y1), Cast.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Fact.Vote{x0, x1, x2} == Types.Fact.Vote{x0, _, y2}: Types.Fact}
        %Cast.is_eq_sound(
          x2,
          y2
        )(
          Shared.Bool.and_true_right(
            Step.is_eq(x1, y1),
            Cast.is_eq(x2, y2)
          )(
            Shared.Bool.and_true_right(
              String.eq(x0, y0),
              Bool.and(Step.is_eq(x1, y1), Cast.is_eq(x2, y2))
            )(h)
          )
        ): {Types.Fact.Vote{x0, x1, x2} == Types.Fact.Vote{x0, x1, _}: Types.Fact}
        {==}

# the laws of Fact.is_eq
def Fact.laws() -> Shared.Eq.Laws(Types.Fact, Fact.is_eq):
  (x => Fact.is_eq_refl(x), x => y => Fact.is_eq_sound(x, y))

# Fact.is_eq gives what the codes give: two facts are the same when
# their words are
def Fact.is_eq_code(
  +a: Types.Fact,
  +b: Types.Fact
) -> {Fact.is_eq(a, b) == Codes.Code.is_eq(~Types.Fact, ~Fact.code, a, b): Bool}:
  Shared.Eq.agree(
    ~Types.Fact,
    ~Fact.is_eq,
    ~(x => y => Codes.Code.is_eq(~Types.Fact, ~Fact.code, x, y)),
    ~Fact.laws(),
    ~Codes.Code.eq_laws(~Types.Fact, ~Fact.codec()),
    a,
    b
  )

# Fact.is_eq is the test of the words of two facts
def Fact.is_eq_words(
  +x: Types.Fact,
  +y: Types.Fact
) -> {Fact.is_eq(x, y) == Crits.Key.is_eq(Fact.words(x), Fact.words(y)): Bool}:
  Equal.trans(
    Bool,
    Fact.is_eq(x, y),
    Shared.List.is_eq(~U32, ~U32.is_eq, Fact.words(x), Fact.words(y)),
    Crits.Key.is_eq(Fact.words(x), Fact.words(y)),
    Fact.is_eq_code(x, y),
    Equal.sym(
      Bool,
      Crits.Key.is_eq(Fact.words(x), Fact.words(y)),
      Shared.List.is_eq(~U32, ~U32.is_eq, Fact.words(x), Fact.words(y)),
      Crits.Key.is_eq_list(Fact.words(x), Fact.words(y))
    )
  )

# two facts with the same words are the same
def Fact.words_inj(
  +a: Types.Fact,
  +b: Types.Fact
) -> {Fact.words(a) == Fact.words(b): List<&2, U32>} -> {a == b: Types.Fact}:
  Ledgers.Book.code_value(~Types.Fact, ~Fact.codec(), a, b, [], [])

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Names
# -----

# the words that name the request r of the id i: the code of i, then of r
def Named.code(i: Ledgers.Id, r: Spec.Request) -> List<&2, U32>:
  Ledgers.Id.code(i, Request.code(r, []))

# two requests with one name have the same id and are the same request
def Named.code_names(
  +i: Ledgers.Id,
  +r: Spec.Request,
  +j: Ledgers.Id,
  +s: Spec.Request
) -> {
  Named.code(i, r) == Named.code(j, s): List<&2, U32>
} -> {i == j: Ledgers.Id}
  & {r == s: Spec.Request}:
  +e =>
    (
      Ledgers.Book.code_value(
        ~Ledgers.Id,
        ~Ledgers.Id.codec(),
        i,
        j,
        Request.code(r, []),
        Request.code(s, [])
      )(e),
      Ledgers.Book.code_value(
        ~Spec.Request,
        ~Request.codec(),
        r,
        s,
        [],
        []
      )(
        Ledgers.Book.code_rest(
          ~Ledgers.Id,
          ~Ledgers.Id.codec(),
          i,
          j,
          Request.code(r, []),
          Request.code(s, [])
        )(e)
      )
    )
