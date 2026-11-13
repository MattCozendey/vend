import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
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

# the words of the request x: its code
def Request.words(x: Spec.Request) -> List<&2, U32>:
  Request.code(x, [])

# a and b are the same request: they have the same words
def Request.is_eq(a: Spec.Request, b: Spec.Request) -> Bool:
  Codes.Code.is_eq(~Spec.Request, ~Request.code, a, b)

# the laws of Request.is_eq
def Request.laws() -> Shared.Eq.Laws(Spec.Request, Request.is_eq):
  Codes.Code.eq_laws(~Spec.Request, ~Request.codec())

# Request.is_eq is True for a request and itself
def Request.is_eq_refl(a: Spec.Request) -> {Request.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Spec.Request, ~Request.is_eq, Request.laws(), a)

# Request.is_eq is True only for equal requests
def Request.is_eq_sound(
  a: Spec.Request,
  b: Spec.Request
) -> {Request.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Request}:
  Shared.Eq.sound(~Spec.Request, ~Request.is_eq, Request.laws(), a, b)

# the words of the ask x: its code
def Ask.words(x: Types.Ask) -> List<&2, U32>:
  Ask.code(x, [])

# a and b are the same ask: they have the same words
def Ask.is_eq(a: Types.Ask, b: Types.Ask) -> Bool:
  Codes.Code.is_eq(~Types.Ask, ~Ask.code, a, b)

# the laws of Ask.is_eq
def Ask.laws() -> Shared.Eq.Laws(Types.Ask, Ask.is_eq):
  Codes.Code.eq_laws(~Types.Ask, ~Ask.codec())

# Ask.is_eq is True for a ask and itself
def Ask.is_eq_refl(a: Types.Ask) -> {Ask.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Types.Ask, ~Ask.is_eq, Ask.laws(), a)

# Ask.is_eq is True only for equal asks
def Ask.is_eq_sound(
  a: Types.Ask,
  b: Types.Ask
) -> {Ask.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Ask}:
  Shared.Eq.sound(~Types.Ask, ~Ask.is_eq, Ask.laws(), a, b)

# the words of the pick x: its code
def Pick.words(x: Types.Pick) -> List<&2, U32>:
  Pick.code(x, [])

# a and b are the same pick: they have the same words
def Pick.is_eq(a: Types.Pick, b: Types.Pick) -> Bool:
  Codes.Code.is_eq(~Types.Pick, ~Pick.code, a, b)

# the laws of Pick.is_eq
def Pick.laws() -> Shared.Eq.Laws(Types.Pick, Pick.is_eq):
  Codes.Code.eq_laws(~Types.Pick, ~Pick.codec())

# Pick.is_eq is True for a pick and itself
def Pick.is_eq_refl(a: Types.Pick) -> {Pick.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Types.Pick, ~Pick.is_eq, Pick.laws(), a)

# Pick.is_eq is True only for equal picks
def Pick.is_eq_sound(
  a: Types.Pick,
  b: Types.Pick
) -> {Pick.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Pick}:
  Shared.Eq.sound(~Types.Pick, ~Pick.is_eq, Pick.laws(), a, b)

# two picks with the same words are the same
def Pick.words_inj(
  +a: Types.Pick,
  +b: Types.Pick
) -> {Pick.words(a) == Pick.words(b): List<&2, U32>} -> {a == b: Types.Pick}:
  Ledgers.Book.code_value(~Types.Pick, ~Pick.codec(), a, b, [], [])

# the words of the step x: its code
def Step.words(x: Types.Step) -> List<&2, U32>:
  Step.code(x, [])

# a and b are the same step: they have the same words
def Step.is_eq(a: Types.Step, b: Types.Step) -> Bool:
  Codes.Code.is_eq(~Types.Step, ~Step.code, a, b)

# the laws of Step.is_eq
def Step.laws() -> Shared.Eq.Laws(Types.Step, Step.is_eq):
  Codes.Code.eq_laws(~Types.Step, ~Step.codec())

# Step.is_eq is True for a step and itself
def Step.is_eq_refl(a: Types.Step) -> {Step.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Types.Step, ~Step.is_eq, Step.laws(), a)

# Step.is_eq is True only for equal steps
def Step.is_eq_sound(
  a: Types.Step,
  b: Types.Step
) -> {Step.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Step}:
  Shared.Eq.sound(~Types.Step, ~Step.is_eq, Step.laws(), a, b)

# two steps with the same words are the same
def Step.words_inj(
  +a: Types.Step,
  +b: Types.Step
) -> {Step.words(a) == Step.words(b): List<&2, U32>} -> {a == b: Types.Step}:
  Ledgers.Book.code_value(~Types.Step, ~Step.codec(), a, b, [], [])

# the words of the cast x: its code
def Cast.words(x: Types.Cast) -> List<&2, U32>:
  Cast.code(x, [])

# a and b are the same cast: they have the same words
def Cast.is_eq(a: Types.Cast, b: Types.Cast) -> Bool:
  Codes.Code.is_eq(~Types.Cast, ~Cast.code, a, b)

# the laws of Cast.is_eq
def Cast.laws() -> Shared.Eq.Laws(Types.Cast, Cast.is_eq):
  Codes.Code.eq_laws(~Types.Cast, ~Cast.codec())

# Cast.is_eq is True for a cast and itself
def Cast.is_eq_refl(a: Types.Cast) -> {Cast.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Types.Cast, ~Cast.is_eq, Cast.laws(), a)

# Cast.is_eq is True only for equal casts
def Cast.is_eq_sound(
  a: Types.Cast,
  b: Types.Cast
) -> {Cast.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Cast}:
  Shared.Eq.sound(~Types.Cast, ~Cast.is_eq, Cast.laws(), a, b)

# two casts with the same words are the same
def Cast.words_inj(
  +a: Types.Cast,
  +b: Types.Cast
) -> {Cast.words(a) == Cast.words(b): List<&2, U32>} -> {a == b: Types.Cast}:
  Ledgers.Book.code_value(~Types.Cast, ~Cast.codec(), a, b, [], [])

# the words of the fact x: its code
def Fact.words(x: Types.Fact) -> List<&2, U32>:
  Fact.code(x, [])

# a and b are the same fact: they have the same words
def Fact.is_eq(a: Types.Fact, b: Types.Fact) -> Bool:
  Codes.Code.is_eq(~Types.Fact, ~Fact.code, a, b)

# the laws of Fact.is_eq
def Fact.laws() -> Shared.Eq.Laws(Types.Fact, Fact.is_eq):
  Codes.Code.eq_laws(~Types.Fact, ~Fact.codec())

# Fact.is_eq is True for a fact and itself
def Fact.is_eq_refl(a: Types.Fact) -> {Fact.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Types.Fact, ~Fact.is_eq, Fact.laws(), a)

# Fact.is_eq is True only for equal facts
def Fact.is_eq_sound(
  a: Types.Fact,
  b: Types.Fact
) -> {Fact.is_eq(a, b) == True{}: Bool} -> {a == b: Types.Fact}:
  Shared.Eq.sound(~Types.Fact, ~Fact.is_eq, Fact.laws(), a, b)

# two facts with the same words are the same
def Fact.words_inj(
  +a: Types.Fact,
  +b: Types.Fact
) -> {Fact.words(a) == Fact.words(b): List<&2, U32>} -> {a == b: Types.Fact}:
  Ledgers.Book.code_value(~Types.Fact, ~Fact.codec(), a, b, [], [])

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
