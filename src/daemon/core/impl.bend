import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/text.bend as Texts
import ../shared/shared/trie.bend as Tries
import ./spec.bend as Spec

# The proofs of the core's laws.

# Codes
# -----

# a request ID reads back
def Id.code_read(
  i: Ledgers.Id,
  r: List<&2, U32>
) -> {
  Spec.Id.code.read(Spec.Id.code(i, r)) == Some{Codes.Read{i, r}}: Maybe<&2, Codes.Read<Ledgers.Id>>
}:
  match i:
    case Ledgers.Id{writer, +request}:
      +r = r
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(
          Codes.Code.text(
            writer,
            Codes.Code.count(Codes.Code.length(request), Codes.Code.chars(request, r))
          )
        ),
        Some{
          Codes.Read{
            writer,
            Codes.Code.count(Codes.Code.length(request), Codes.Code.chars(request, r))
          }
        },
        Codes.Code.text_read(
          writer,
          Codes.Code.count(Codes.Code.length(request), Codes.Code.chars(request, r))
        )
      ):
        {
          Codes.Read.then(
            String,
            Ledgers.Id,
            _,
            w => r => Codes.Read.then(
              String,
              Ledgers.Id,
              Codes.Code.text.read(r),
              q => r2 => Some{Codes.Read{Ledgers.Id{w, q}, r2}}
            )
          )
            == Some{Codes.Read{Ledgers.Id{writer, request}, r}}: Maybe<&2, Codes.Read<Ledgers.Id>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(request, r)),
        Some{Codes.Read{request, r}},
        Codes.Code.text_read(request, r)
      ):
        {
          Codes.Read.then(
            String,
            Ledgers.Id,
            _,
            q => r2 => Some{Codes.Read{Ledgers.Id{writer, q}, r2}}
          )
            == Some{Codes.Read{Ledgers.Id{writer, request}, r}}: Maybe<&2, Codes.Read<Ledgers.Id>>
        }
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a resource name reads back
def Name.code_read(
  n: Resources.Name,
  r: List<&2, U32>
) -> {
  Spec.Name.code.read(
    Spec.Name.code(n, r)
  )
    == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Resources.Name>>
}:
  match n:
    case Resources.Name{text}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(text, r)),
        Some{Codes.Read{text, r}},
        Codes.Code.text_read(text, r)
      ):
        {
          Codes.Read.then(
            String,
            Resources.Name,
            _,
            t => r => Some{Codes.Read{Resources.Name{t}, r}}
          )
            == Some{Codes.Read{Resources.Name{text}, r}}: Maybe<&2, Codes.Read<Resources.Name>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a token reads back
def U32.code_read(
  x: U32,
  r: List<&2, U32>
) -> {
  Spec.U32.code.read(Spec.U32.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<U32>>
}:
  {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a line reads back
def Line.code_read(
  l: Spec.Line,
  r: List<&2, U32>
) -> {
  Spec.Line.code.read(
    Spec.Line.code(l, r)
  )
    == Some{Codes.Read{l, r}}: Maybe<&2, Codes.Read<Spec.Line>>
}:
  match l:
    case Spec.Line.branch{name}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(name, r)),
        Some{Codes.Read{name, r}},
        Codes.Code.text_read(name, r)
      ):
        {
          Codes.Read.then(
            String,
            Spec.Line,
            _,
            n => r2 => Some{
              Codes.Read{
                Shared.Bool.when(
                  Spec.Line,
                  U32.is_eq(0, 0),
                  u => Spec.Line.branch{n},
                  u => Spec.Line.group{n}
                ),
                r2
              }
            }
          )
            == Some{Codes.Read{Spec.Line.branch{name}, r}}: Maybe<&2, Codes.Read<Spec.Line>>
        }
      {==}
    case Spec.Line.group{name1}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(name1, r)),
        Some{Codes.Read{name1, r}},
        Codes.Code.text_read(name1, r)
      ):
        {
          Codes.Read.then(
            String,
            Spec.Line,
            _,
            n => r2 => Some{
              Codes.Read{
                Shared.Bool.when(
                  Spec.Line,
                  U32.is_eq(1, 0),
                  u => Spec.Line.branch{n},
                  u => Spec.Line.group{n}
                ),
                r2
              }
            }
          )
            == Some{Codes.Read{Spec.Line.group{name1}, r}}: Maybe<&2, Codes.Read<Spec.Line>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a member reads back
def Member.code_read(
  m: Spec.Member,
  r: List<&2, U32>
) -> {
  Spec.Member.code.read(
    Spec.Member.code(m, r)
  )
    == Some{Codes.Read{m, r}}: Maybe<&2, Codes.Read<Spec.Member>>
}:
  match m:
    case Spec.Member.node{name}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(name, r)),
        Some{Codes.Read{name, r}},
        Codes.Code.text_read(name, r)
      ):
        {
          Codes.Read.then(
            String,
            Spec.Member,
            _,
            n => r2 => Some{
              Codes.Read{
                Shared.Bool.when(
                  Spec.Member,
                  U32.is_eq(0, 0),
                  u => Spec.Member.node{n},
                  u => Spec.Member.group{n}
                ),
                r2
              }
            }
          )
            == Some{Codes.Read{Spec.Member.node{name}, r}}: Maybe<&2, Codes.Read<Spec.Member>>
        }
      {==}
    case Spec.Member.group{name1}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(name1, r)),
        Some{Codes.Read{name1, r}},
        Codes.Code.text_read(name1, r)
      ):
        {
          Codes.Read.then(
            String,
            Spec.Member,
            _,
            n => r2 => Some{
              Codes.Read{
                Shared.Bool.when(
                  Spec.Member,
                  U32.is_eq(1, 0),
                  u => Spec.Member.node{n},
                  u => Spec.Member.group{n}
                ),
                r2
              }
            }
          )
            == Some{Codes.Read{Spec.Member.group{name1}, r}}: Maybe<&2, Codes.Read<Spec.Member>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the laws of the token code
def U32.code_laws() -> Codes.Code.Laws(U32, Spec.U32.code, Spec.U32.code.read):
  x => r => U32.code_read(x, r)

# the laws of the request ID code
def Id.code_laws() -> Codes.Code.Laws(Ledgers.Id, Spec.Id.code, Spec.Id.code.read):
  x => r => Id.code_read(x, r)

# the laws of the member code
def Member.code_laws() -> Codes.Code.Laws(Spec.Member, Spec.Member.code, Spec.Member.code.read):
  x => r => Member.code_read(x, r)

# the laws of the line code
def Line.code_laws() -> Codes.Code.Laws(Spec.Line, Spec.Line.code, Spec.Line.code.read):
  x => r => Line.code_read(x, r)

# the laws of the text code
def Text.code_laws() -> Codes.Code.Laws(String, Codes.Code.text, Codes.Code.text.read):
  x => r => Codes.Code.text_read(x, r)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a content reads back
def Content.code_read(
  c: Spec.Content,
  r: List<&2, U32>
) -> {
  Spec.Content.code.read(
    Spec.Content.code(c, r)
  )
    == Some{Codes.Read{c, r}}: Maybe<&2, Codes.Read<Spec.Content>>
}:
  match c:
    case Spec.Content.bytes{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<List<&2, U32>>>,
        Codes.Code.list.read(
          ~U32,
          ~Spec.U32.code.read,
          Codes.Code.list(~U32, ~Spec.U32.code, v0, r)
        ),
        Some{Codes.Read{v0, r}},
        Codes.Code.list_read(~U32, ~Spec.U32.code, ~Spec.U32.code.read, ~U32.code_laws(), v0, r)
      ):
        {
          Codes.Read.then(
            List<&2, U32>,
            Spec.Content,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Content.bytes{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Content.bytes{v0}, r}}: Maybe<&2, Codes.Read<Spec.Content>>
        }
      {==}
    case Spec.Content.of{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Ledgers.Id>>,
        Spec.Id.code.read(Spec.Id.code(v0, r)),
        Some{Codes.Read{v0, r}},
        Id.code_read(v0, r)
      ):
        {
          Codes.Read.then(
            Ledgers.Id,
            Spec.Content,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Content.of{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Content.of{v0}, r}}: Maybe<&2, Codes.Read<Spec.Content>>
        }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a change reads back
def Change.code_read(
  c: Spec.Change,
  +r: List<&2, U32>
) -> {
  Spec.Change.code.read(
    Spec.Change.code(c, r)
  )
    == Some{Codes.Read{c, r}}: Maybe<&2, Codes.Read<Spec.Change>>
}:
  match c:
    case Spec.Change.make{v0, +v1, +v2}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Spec.Line>>,
        Spec.Line.code.read(
          Spec.Line.code(
            v0,
            Codes.Code.maybe(
              ~Ledgers.Id,
              ~Spec.Id.code,
              v1,
              Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
            )
          )
        ),
        Some{
          Codes.Read{
            v0,
            Codes.Code.maybe(
              ~Ledgers.Id,
              ~Spec.Id.code,
              v1,
              Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
            )
          }
        },
        Line.code_read(
          v0,
          Codes.Code.maybe(
            ~Ledgers.Id,
            ~Spec.Id.code,
            v1,
            Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
          )
        )
      ):
        {
          Codes.Read.then(
            Spec.Line,
            Spec.Change,
            _,
            x0 => q1 => Codes.Read.then(
              Maybe<&2, Ledgers.Id>,
              Spec.Change,
              Codes.Code.maybe.read(~Ledgers.Id, ~Spec.Id.code.read, q1),
              x1 => q2 => Codes.Read.then(
                List<&2, Spec.Member>,
                Spec.Change,
                Codes.Code.list.read(~Spec.Member, ~Spec.Member.code.read, q2),
                x2 => q3 => Some{Codes.Read{Spec.Change.make{x0, x1, x2}, q3}}
              )
            )
          )
            == Some{Codes.Read{Spec.Change.make{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Maybe<&2, Ledgers.Id>>>,
        Codes.Code.maybe.read(
          ~Ledgers.Id,
          ~Spec.Id.code.read,
          Codes.Code.maybe(
            ~Ledgers.Id,
            ~Spec.Id.code,
            v1,
            Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
          )
        ),
        Some{Codes.Read{v1, Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)}},
        Codes.Code.maybe_read(
          ~Ledgers.Id,
          ~Spec.Id.code,
          ~Spec.Id.code.read,
          Id.code_laws(),
          v1,
          Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
        )
      ):
        {
          Codes.Read.then(
            Maybe<&2, Ledgers.Id>,
            Spec.Change,
            _,
            x1 => q2 => Codes.Read.then(
              List<&2, Spec.Member>,
              Spec.Change,
              Codes.Code.list.read(~Spec.Member, ~Spec.Member.code.read, q2),
              x2 => q3 => Some{Codes.Read{Spec.Change.make{v0, x1, x2}, q3}}
            )
          )
            == Some{Codes.Read{Spec.Change.make{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<List<&2, Spec.Member>>>,
        Codes.Code.list.read(
          ~Spec.Member,
          ~Spec.Member.code.read,
          Codes.Code.list(~Spec.Member, ~Spec.Member.code, v2, r)
        ),
        Some{Codes.Read{v2, r}},
        Codes.Code.list_read(
          ~Spec.Member,
          ~Spec.Member.code,
          ~Spec.Member.code.read,
          ~Member.code_laws(),
          v2,
          r
        )
      ):
        {
          Codes.Read.then(
            List<&2, Spec.Member>,
            Spec.Change,
            _,
            x2 => q3 => Some{Codes.Read{Spec.Change.make{v0, v1, x2}, q3}}
          )
            == Some{Codes.Read{Spec.Change.make{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.own{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<List<&2, String>>>,
        Codes.Code.list.read(
          ~String,
          ~Codes.Code.text.read,
          Codes.Code.list(~String, ~Codes.Code.text, v0, r)
        ),
        Some{Codes.Read{v0, r}},
        Codes.Code.list_read(
          ~String,
          ~Codes.Code.text,
          ~Codes.Code.text.read,
          ~Text.code_laws(),
          v0,
          r
        )
      ):
        {
          Codes.Read.then(
            List<&2, String>,
            Spec.Change,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Change.own{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Change.own{v0}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.write{v0, +v1, +v2}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Resources.Name>>,
        Spec.Name.code.read(
          Spec.Name.code(
            v0,
            Codes.Code.maybe(~Ledgers.Id, ~Spec.Id.code, v1, Spec.Content.code(v2, r))
          )
        ),
        Some{
          Codes.Read{v0, Codes.Code.maybe(~Ledgers.Id, ~Spec.Id.code, v1, Spec.Content.code(v2, r))}
        },
        Name.code_read(
          v0,
          Codes.Code.maybe(~Ledgers.Id, ~Spec.Id.code, v1, Spec.Content.code(v2, r))
        )
      ):
        {
          Codes.Read.then(
            Resources.Name,
            Spec.Change,
            _,
            x0 => q1 => Codes.Read.then(
              Maybe<&2, Ledgers.Id>,
              Spec.Change,
              Codes.Code.maybe.read(~Ledgers.Id, ~Spec.Id.code.read, q1),
              x1 => q2 => Codes.Read.then(
                Spec.Content,
                Spec.Change,
                Spec.Content.code.read(q2),
                x2 => q3 => Some{Codes.Read{Spec.Change.write{x0, x1, x2}, q3}}
              )
            )
          )
            == Some{
              Codes.Read{Spec.Change.write{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Maybe<&2, Ledgers.Id>>>,
        Codes.Code.maybe.read(
          ~Ledgers.Id,
          ~Spec.Id.code.read,
          Codes.Code.maybe(~Ledgers.Id, ~Spec.Id.code, v1, Spec.Content.code(v2, r))
        ),
        Some{Codes.Read{v1, Spec.Content.code(v2, r)}},
        Codes.Code.maybe_read(
          ~Ledgers.Id,
          ~Spec.Id.code,
          ~Spec.Id.code.read,
          Id.code_laws(),
          v1,
          Spec.Content.code(v2, r)
        )
      ):
        {
          Codes.Read.then(
            Maybe<&2, Ledgers.Id>,
            Spec.Change,
            _,
            x1 => q2 => Codes.Read.then(
              Spec.Content,
              Spec.Change,
              Spec.Content.code.read(q2),
              x2 => q3 => Some{Codes.Read{Spec.Change.write{v0, x1, x2}, q3}}
            )
          )
            == Some{
              Codes.Read{Spec.Change.write{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Spec.Content>>,
        Spec.Content.code.read(Spec.Content.code(v2, r)),
        Some{Codes.Read{v2, r}},
        Content.code_read(v2, r)
      ):
        {
          Codes.Read.then(
            Spec.Content,
            Spec.Change,
            _,
            x2 => q3 => Some{Codes.Read{Spec.Change.write{v0, v1, x2}, q3}}
          )
            == Some{
              Codes.Read{Spec.Change.write{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.resolve{v0, +v1, +v2}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Ledgers.Id>>,
        Spec.Id.code.read(Spec.Id.code(v0, Spec.Name.code(v1, Spec.Content.code(v2, r)))),
        Some{Codes.Read{v0, Spec.Name.code(v1, Spec.Content.code(v2, r))}},
        Id.code_read(v0, Spec.Name.code(v1, Spec.Content.code(v2, r)))
      ):
        {
          Codes.Read.then(
            Ledgers.Id,
            Spec.Change,
            _,
            x0 => q1 => Codes.Read.then(
              Resources.Name,
              Spec.Change,
              Spec.Name.code.read(q1),
              x1 => q2 => Codes.Read.then(
                Spec.Content,
                Spec.Change,
                Spec.Content.code.read(q2),
                x2 => q3 => Some{Codes.Read{Spec.Change.resolve{x0, x1, x2}, q3}}
              )
            )
          )
            == Some{
              Codes.Read{Spec.Change.resolve{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Resources.Name>>,
        Spec.Name.code.read(Spec.Name.code(v1, Spec.Content.code(v2, r))),
        Some{Codes.Read{v1, Spec.Content.code(v2, r)}},
        Name.code_read(v1, Spec.Content.code(v2, r))
      ):
        {
          Codes.Read.then(
            Resources.Name,
            Spec.Change,
            _,
            x1 => q2 => Codes.Read.then(
              Spec.Content,
              Spec.Change,
              Spec.Content.code.read(q2),
              x2 => q3 => Some{Codes.Read{Spec.Change.resolve{v0, x1, x2}, q3}}
            )
          )
            == Some{
              Codes.Read{Spec.Change.resolve{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Spec.Content>>,
        Spec.Content.code.read(Spec.Content.code(v2, r)),
        Some{Codes.Read{v2, r}},
        Content.code_read(v2, r)
      ):
        {
          Codes.Read.then(
            Spec.Content,
            Spec.Change,
            _,
            x2 => q3 => Some{Codes.Read{Spec.Change.resolve{v0, v1, x2}, q3}}
          )
            == Some{
              Codes.Read{Spec.Change.resolve{v0, v1, v2}, r}
            }: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.merge{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Ledgers.Id>>,
        Spec.Id.code.read(Spec.Id.code(v0, r)),
        Some{Codes.Read{v0, r}},
        Id.code_read(v0, r)
      ):
        {
          Codes.Read.then(
            Ledgers.Id,
            Spec.Change,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Change.merge{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Change.merge{v0}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.move{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Ledgers.Id>>,
        Spec.Id.code.read(Spec.Id.code(v0, r)),
        Some{Codes.Read{v0, r}},
        Id.code_read(v0, r)
      ):
        {
          Codes.Read.then(
            Ledgers.Id,
            Spec.Change,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Change.move{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Change.move{v0}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.mark{v0, +v1}:
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(v0, Codes.Code.text(v1, r))),
        Some{Codes.Read{v0, Codes.Code.text(v1, r)}},
        Codes.Code.text_read(v0, Codes.Code.text(v1, r))
      ):
        {
          Codes.Read.then(
            String,
            Spec.Change,
            _,
            x0 => q1 => Codes.Read.then(
              String,
              Spec.Change,
              Codes.Code.text.read(q1),
              x1 => q2 => Some{Codes.Read{Spec.Change.mark{x0, x1}, q2}}
            )
          )
            == Some{Codes.Read{Spec.Change.mark{v0, v1}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<String>>,
        Codes.Code.text.read(Codes.Code.text(v1, r)),
        Some{Codes.Read{v1, r}},
        Codes.Code.text_read(v1, r)
      ):
        {
          Codes.Read.then(
            String,
            Spec.Change,
            _,
            x1 => q2 => Some{Codes.Read{Spec.Change.mark{v0, x1}, q2}}
          )
            == Some{Codes.Read{Spec.Change.mark{v0, v1}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}
    case Spec.Change.members{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<List<&2, Spec.Member>>>,
        Codes.Code.list.read(
          ~Spec.Member,
          ~Spec.Member.code.read,
          Codes.Code.list(~Spec.Member, ~Spec.Member.code, v0, r)
        ),
        Some{Codes.Read{v0, r}},
        Codes.Code.list_read(
          ~Spec.Member,
          ~Spec.Member.code,
          ~Spec.Member.code.read,
          ~Member.code_laws(),
          v0,
          r
        )
      ):
        {
          Codes.Read.then(
            List<&2, Spec.Member>,
            Spec.Change,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Change.members{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Change.members{v0}, r}}: Maybe<&2, Codes.Read<Spec.Change>>
        }
      {==}

# a request reads back
def Ask.code_read(
  q: Spec.Ask,
  +r: List<&2, U32>
) -> {
  Spec.Ask.code.read(Spec.Ask.code(q, r)) == Some{Codes.Read{q, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
}:
  match q:
    case Spec.Ask.start{v0}:
      %Equal.sym(
        Maybe<&2, Codes.Read<List<&2, String>>>,
        Codes.Code.list.read(
          ~String,
          ~Codes.Code.text.read,
          Codes.Code.list(~String, ~Codes.Code.text, v0, r)
        ),
        Some{Codes.Read{v0, r}},
        Codes.Code.list_read(
          ~String,
          ~Codes.Code.text,
          ~Codes.Code.text.read,
          ~Text.code_laws(),
          v0,
          r
        )
      ):
        {
          Codes.Read.then(
            List<&2, String>,
            Spec.Ask,
            _,
            x0 => q1 => Some{Codes.Read{Spec.Ask.start{x0}, q1}}
          )
            == Some{Codes.Read{Spec.Ask.start{v0}, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
        }
      {==}
    case Spec.Ask.on{v0, +v1, +v2}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Ledgers.Id>>,
        Spec.Id.code.read(
          Spec.Id.code(
            v0,
            Codes.Code.maybe(~Spec.Line, ~Spec.Line.code, v1, Spec.Change.code(v2, r))
          )
        ),
        Some{
          Codes.Read{v0, Codes.Code.maybe(~Spec.Line, ~Spec.Line.code, v1, Spec.Change.code(v2, r))}
        },
        Id.code_read(v0, Codes.Code.maybe(~Spec.Line, ~Spec.Line.code, v1, Spec.Change.code(v2, r)))
      ):
        {
          Codes.Read.then(
            Ledgers.Id,
            Spec.Ask,
            _,
            x0 => q1 => Codes.Read.then(
              Maybe<&2, Spec.Line>,
              Spec.Ask,
              Codes.Code.maybe.read(~Spec.Line, ~Spec.Line.code.read, q1),
              x1 => q2 => Codes.Read.then(
                Spec.Change,
                Spec.Ask,
                Spec.Change.code.read(q2),
                x2 => q3 => Some{Codes.Read{Spec.Ask.on{x0, x1, x2}, q3}}
              )
            )
          )
            == Some{Codes.Read{Spec.Ask.on{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Maybe<&2, Spec.Line>>>,
        Codes.Code.maybe.read(
          ~Spec.Line,
          ~Spec.Line.code.read,
          Codes.Code.maybe(~Spec.Line, ~Spec.Line.code, v1, Spec.Change.code(v2, r))
        ),
        Some{Codes.Read{v1, Spec.Change.code(v2, r)}},
        Codes.Code.maybe_read(
          ~Spec.Line,
          ~Spec.Line.code,
          ~Spec.Line.code.read,
          Line.code_laws(),
          v1,
          Spec.Change.code(v2, r)
        )
      ):
        {
          Codes.Read.then(
            Maybe<&2, Spec.Line>,
            Spec.Ask,
            _,
            x1 => q2 => Codes.Read.then(
              Spec.Change,
              Spec.Ask,
              Spec.Change.code.read(q2),
              x2 => q3 => Some{Codes.Read{Spec.Ask.on{v0, x1, x2}, q3}}
            )
          )
            == Some{Codes.Read{Spec.Ask.on{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
        }
      %Equal.sym(
        Maybe<&2, Codes.Read<Spec.Change>>,
        Spec.Change.code.read(Spec.Change.code(v2, r)),
        Some{Codes.Read{v2, r}},
        Change.code_read(v2, r)
      ):
        {
          Codes.Read.then(
            Spec.Change,
            Spec.Ask,
            _,
            x2 => q3 => Some{Codes.Read{Spec.Ask.on{v0, v1, x2}, q3}}
          )
            == Some{Codes.Read{Spec.Ask.on{v0, v1, v2}, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
        }
      {==}

# the laws of the request code
def Ask.code_laws() -> Codes.Code.Laws(Spec.Ask, Spec.Ask.code, Spec.Ask.code.read):
  x => r => Ask.code_read(x, r)

# the laws of Spec.Ask.is_eq: two requests are the same exactly when their codes
# are
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.is_eq):
  Codes.Code.eq_laws(~Spec.Ask, ~Spec.Ask.code, ~Spec.Ask.code.read, ~Ask.code_laws())

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners take a write whose base is ready and whose resource did not change
def Write.takes(
  s: Spec.State(),
  r: Ledgers.Id,
  b: String,
  name: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Texts.Bytes(),
  xs: List<&2, Ledgers.Step<Spec.Ask>>
) -> {
  Spec.Judge.ready_maybe(s, base) == Some{True{}}: Maybe<&2, Bool>
} -> {
  Spec.Bytes.same(
    Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
    Spec.Res.of(s, name, base)
  )
    == True{}: Bool
} -> {
  Spec.Node.judge(
    s,
    Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}},
    xs
  )
    == Some{True{}}: Maybe<&2, Bool>
}:
  hr => hc =>
    %Equal.sym(Maybe<&2, Bool>, Spec.Judge.ready_maybe(s, base), Some{True{}}, hr):
      {
        Spec.Judge.then(
          _,
          u => Spec.Judge.then(
            Spec.Judge.content(s, Spec.Content.bytes{x}),
            w => Some{
              Spec.Bytes.same(
                Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
                Spec.Res.of(s, name, base)
              )
            }
          )
        )
          == Some{True{}}: Maybe<&2, Bool>
      }
    %Equal.sym(
      Bool,
      Spec.Bytes.same(
        Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
        Spec.Res.of(s, name, base)
      ),
      True{},
      hc
    ):
      {Some{_} == Some{True{}}: Maybe<&2, Bool>}
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.Node.write_written(n, s, e, r, b, name, base, x, h):
  +h1 => ht => hg => hv => hr => hc =>
    +hs = Ledgers.State.ask_decides(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      },
      Spec.Line.chain(r, Some{Spec.Line.branch{b}}),
      None{},
      None{},
      h,
      True{}
    )(
      h1
    )(
      {==}
    )(
      ht
    )(
      hg
    )(
      hv
    )(
      Write.takes(
        Spec.Node.taken(
          s,
          e,
          Spec.Ask.on{
            r,
            Some{Spec.Line.branch{b}},
            Spec.Change.write{name, base, Spec.Content.bytes{x}}
          }
        ),
        r,
        b,
        name,
        base,
        x,
        Spec.Node.steps(
          Spec.Node.taken(
            s,
            e,
            Spec.Ask.on{
              r,
              Some{Spec.Line.branch{b}},
              Spec.Change.write{name, base, Spec.Content.bytes{x}}
            }
          ),
          r,
          Some{Spec.Line.branch{b}}
        )
      )(hr)(hc)
    )
    +ha = Ledgers.State.ask_holds(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }
    )(h1)
    ((
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Answer.of(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Answer.taken(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        {==}), (
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Res.of(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{Spec.Envelope.of(e)}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Res.go(Spec.State.fuel(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}})), Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Src.at(Spec.Envelope.of(e), _), name) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Bool, Resources.Name.is_eq(name, name), True{}, Resources.Name.is_eq_refl(name)):
          {Shared.Bool.when(Maybe<&2, Texts.Bytes()>, _, u => Some{x}, u => Spec.Res.go(Nat.double(Tries.Trie.size(Ledgers.Cell<Ledgers.Entry<Spec.Ask>>, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}))), Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Src.before{Spec.Envelope.of(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}, name)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        {==}))
