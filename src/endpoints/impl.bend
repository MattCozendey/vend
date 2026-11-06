import Base
import ../shared.bend as Shared
import ./spec.bend as Spec
# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- proof binders whose other use is inside a rewrite motive or an erased argument; the checker accepts them

# Proofs of the stream laws. Most are a split on the stream and evaluation;
# the write laws go through the two Bool.when lemmas below.
def Word.cmp_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{}: Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+np:
      match a:
        case WCon{+head, tail}:
          match head:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(False{}, False{}, _) == EQ{}: Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(True{}, True{}, _) == EQ{}: Cmp}
              {==}

def U32.is_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{}: Bool}:
  match x:
    case U32{w}:
      %Equal.sym(
        Cmp,
        Word.cmp(32n, w, w),
        EQ{},
        Word.cmp_refl(32n, w)
      ): {Cmp.is_eq(_) == True{}: Bool}
      {==}

def Bytes.is_eq_refl(b: Shared.Bytes()) -> {Shared.Bytes.is_eq(b, b) == True{}: Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+head, tail}:
      match head:
        case U32{data}:
          Equal.sym(
            Bool,
            True{},
            Shared.Bytes.is_eq(U32{data} <> tail, U32{data} <> tail),
            (%Equal.sym(
              Cmp,
              Word.cmp(32n, data, data),
              EQ{},
              Word.cmp_refl(32n, data)
            ): {
              True{} == List.all.if(u => Shared.Bytes.is_eq(tail, tail), Cmp.is_eq(_)): Bool
            }; (%Equal.sym(
              Bool,
              Shared.Bytes.is_eq(tail, tail),
              True{},
              Bytes.is_eq_refl(tail)
            ): {True{} == _: Bool}; {==}))
          )

def When.is_fail(
  -A: Data,
  b: Bool,
  x: A,
  f: Spec.Refused
) -> {
  Result.is_fail(
    &2,
    &2,
    Spec.Refused,
    A,
    Shared.Bool.when(Result<&2, &2, Spec.Refused, A>, b, u => Done{x}, u => Fail{f})
  )
    == Bool.not(b): Bool
}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def When.done_eq(
  -A: Data,
  b: Bool,
  x: A,
  f: Spec.Refused,
  s: A
) -> {
  Shared.Bool.when(
    Result<&2, &2, Spec.Refused, A>,
    b,
    u => Done{x},
    u => Fail{f}
  )
    == Done{s}: Result<&2, &2, Spec.Refused, A>
} -> {x == s: A}:
  match b:
    case True{}:
      h => Equal.cong(
        Result<&2, &2, Spec.Refused, A>,
        A,
        r => Result.default(&2, &2, Spec.Refused, A, r, x),
        Done{x},
        Done{s},
        h
      )
    case False{}:
      h => Empty.absurd(
        {x == s: A},
        (%h: Bool.pick(Type, Result.is_done(&2, &2, Spec.Refused, A, _), Empty, Unit); Unit{})
      )

def Spec.unreachable_records_nothing(k, why):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          {==}
        case True{}:
          {==}

def Spec.unreachable_keeps_last(k, why):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          {==}
        case True{}:
          {==}

def Spec.hint_records_nothing(k):
  match k:
    case Spec.Stream{reach, last, +fetching, dirty}:
      match fetching:
        case False{}:
          {==}
        case True{}:
          {==}

def Spec.hint_fetches_once(k):
  match k:
    case Spec.Stream{reach, last, +fetching, dirty}:
      match fetching:
        case False{}:
          {==}
        case True{}:
          {==}

def Spec.hint_is_kept(k):
  match k:
    case Spec.Stream{reach, last, +fetching, dirty}:
      match fetching:
        case False{}:
          {==}
        case True{}:
          {==}

def Spec.same_content_records_nothing(k, bytes, t, h):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          %Equal.sym(Bool, Spec.Stream.knows(last, t), True{}, h):
            {
              Spec.Effect.versions(
                Shared.Bool.when(
                  List<&2, Spec.Effect>,
                  _,
                  u => [],
                  u => [Spec.Record{Spec.Content{bytes, t}}]
                )
              )
                == []: List<&2, Spec.Version>
            }
          {==}
        case True{}:
          %Equal.sym(Bool, Spec.Stream.knows(last, t), True{}, h):
            {
              Spec.Effect.versions(
                List.append(
                  &2,
                  Spec.Effect,
                  Shared.Bool.when(
                    List<&2, Spec.Effect>,
                    _,
                    u => [],
                    u => [Spec.Record{Spec.Content{bytes, t}}]
                  ),
                  [Spec.Send{Spec.Fetch{}}]
                )
              )
                == []: List<&2, Spec.Version>
            }
          {==}

def Spec.new_content_records_once(k, bytes, t, h):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          %Equal.sym(Bool, Spec.Stream.knows(last, t), False{}, h):
            {
              Spec.Effect.versions(
                Shared.Bool.when(
                  List<&2, Spec.Effect>,
                  _,
                  u => [],
                  u => [Spec.Record{Spec.Content{bytes, t}}]
                )
              )
                == [Spec.Content{bytes, t}]: List<&2, Spec.Version>
            }
          {==}
        case True{}:
          %Equal.sym(Bool, Spec.Stream.knows(last, t), False{}, h):
            {
              Spec.Effect.versions(
                List.append(
                  &2,
                  Spec.Effect,
                  Shared.Bool.when(
                    List<&2, Spec.Effect>,
                    _,
                    u => [],
                    u => [Spec.Record{Spec.Content{bytes, t}}]
                  ),
                  [Spec.Send{Spec.Fetch{}}]
                )
              )
                == [Spec.Content{bytes, t}]: List<&2, Spec.Version>
            }
          {==}

def Spec.absent_records_gone(k, t, h):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          %Equal.sym(Maybe<&2, Shared.Bytes()>, last, Some{t}, h):
            {
              Spec.Stepped.versions(
                Spec.Stream.absent(_, False{})
              )
                == [Spec.Gone{}]: List<&2, Spec.Version>
            }
          {==}
        case True{}:
          %Equal.sym(Maybe<&2, Shared.Bytes()>, last, Some{t}, h):
            {
              Spec.Stepped.versions(
                Spec.Stream.absent(_, True{})
              )
                == [Spec.Gone{}]: List<&2, Spec.Version>
            }
          {==}

def Spec.absent_stays_quiet(k, h):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          %Equal.sym(Maybe<&2, Shared.Bytes()>, last, None{}, h):
            {Spec.Stepped.versions(Spec.Stream.absent(_, False{})) == []: List<&2, Spec.Version>}
          {==}
        case True{}:
          %Equal.sym(Maybe<&2, Shared.Bytes()>, last, None{}, h):
            {Spec.Stepped.versions(Spec.Stream.absent(_, True{})) == []: List<&2, Spec.Version>}
          {==}

def Spec.write_refused(k, bytes, t, e):
  +k = k
  +e = e
  When.is_fail(
    Spec.Stepped,
    Spec.Expect.holds(e, k),
    Spec.Stream.wrote(bytes, t, e),
    Spec.Refused{k}
  )

def Spec.write_puts_and_records(k, bytes, t, e, s, h):
  bytes = bytes
  t = t
  +e = e
  +k = k
  eq = When.done_eq(
    Spec.Stepped,
    Spec.Expect.holds(e, k),
    Spec.Stream.wrote(bytes, t, e),
    Spec.Refused{k},
    s
  )(h)
  %eq: (
    {
      Spec.Stepped.commands(_) == [Spec.Put{bytes, e}]: List<&2, Spec.Command>
    }
      & {Spec.Stepped.versions(_) == [Spec.Content{bytes, t}]: List<&2, Spec.Version>}
  )
  ({==}, {==})

def Spec.write_then_fetch_quiet(k, bytes, t, e, s, h):
  bytes = bytes
  +t = t
  +e = e
  +k = k
  eq = When.done_eq(
    Spec.Stepped,
    Spec.Expect.holds(e, k),
    Spec.Stream.wrote(bytes, t, e),
    Spec.Refused{k},
    s
  )(h)
  %eq: {
    Spec.Stepped.versions(
      Spec.Stream.step(Spec.Stepped.stream(_), Spec.Fetched{bytes, t})
    )
      == []: List<&2, Spec.Version>
  }
  %Equal.sym(Bool, Shared.Bytes.is_eq(t, t), True{}, Bytes.is_eq_refl(t)):
    {
      Spec.Effect.versions(
        Shared.Bool.when(
          List<&2, Spec.Effect>,
          _,
          u => [],
          u => [Spec.Record{Spec.Content{bytes, t}}]
        )
      )
        == []: List<&2, Spec.Version>
    }
  {==}

def Spec.absent_ends_fetch(k):
  match k:
    case Spec.Stream{reach, +last, fetching, +dirty}:
      match last:
        case None{}:
          match dirty:
            case False{}:
              {==}
            case True{}:
              {==}
        case Some{value}:
          match dirty:
            case False{}:
              {==}
            case True{}:
              {==}

def Spec.unreachable_ends_fetch(k, why):
  match k:
    case Spec.Stream{reach, last, fetching, +dirty}:
      match dirty:
        case False{}:
          {==}
        case True{}:
          {==}
