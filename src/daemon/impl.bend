import Base
import ../core/impl.bend as CoreImpl
import ../core/spec.bend as Core
import ../journal/impl.bend as J
import ../shared.bend as Shared
import ./spec.bend as Spec

def Spec.Daemon.step(d, l, i):
  +d = d
  +l = l
  Spec.Daemon.stepped(d, Spec.Local.globs(l), Core.Core.step(Spec.Daemon.core(d, l), i))

# Decoding
# --------
# Each reader takes what it needs from the front of the bytes and gives the
# rest, as the journal's readers do.

# n texts, framed as UTF-8, one after another
def Texts.read.go(n: Nat, b: Shared.Bytes()) -> Maybe<&2, J.Got<List<&2, String>>>:
  match n:
    case 0n:
      Some{J.Got{[], b}}
    case 1n+k:
      J.Got.then(
        String,
        List<&2, String>,
        J.Utf8.read(b),
        x => r => J.Got.then(
          List<&2, String>,
          List<&2, String>,
          Texts.read.go(k, r),
          xs => r2 => Some{J.Got{x <> xs, r2}}
        )
      )

# texts: their count, then each
def Texts.read(b: Shared.Bytes()) -> Maybe<&2, J.Got<List<&2, String>>>:
  J.Got.then(Nat, List<&2, String>, J.Leb.read(b), n => r => Texts.read.go(n, r))

# the value of m when it read all of the bytes, else None
def Read.whole(-A: Data, m: Maybe<&2, J.Got<A>>) -> Maybe<&2, A>:
  match m:
    case Some{J.Got{v, Nil{}}}:
      Some{v}
    case _:
      None{}

# a Bool: 0 or 1
def Flag.read(b: Shared.Bytes()) -> Maybe<&2, J.Got<Bool>>:
  match b:
    case Con{0, r}:
      Some{J.Got{False{}, r}}
    case Con{1, r}:
      Some{J.Got{True{}, r}}
    case _:
      None{}

# what a request asks, after its tag
def Body.read(b: Shared.Bytes()) -> Maybe<&2, J.Got<Spec.Body>>:
  match b:
    case Con{0, r}:
      Some{J.Got{Spec.Status{}, r}}
    case Con{1, r}:
      J.Got.then(
        String,
        Spec.Body,
        J.Utf8.read(r),
        u => r2 => J.Got.then(
          List<&2, String>,
          Spec.Body,
          Texts.read(r2),
          gs => r3 => J.Got.then(
            String,
            Spec.Body,
            J.Utf8.read(r3),
            ln => r4 => Some{J.Got{Spec.Mount{u, gs, ln}, r4}}
          )
        )
      )
    case Con{2, r}:
      J.Got.then(String, Spec.Body, J.Utf8.read(r), u => r2 => Some{J.Got{Spec.Unmount{u}, r2}})
    case Con{3, r}:
      J.Got.then(Bool, Spec.Body, Flag.read(r), f => r2 => Some{J.Got{Spec.Stop{f}, r2}})
    case _:
      None{}

def Spec.Request.decode(b):
  Read.whole(
    Spec.Request,
    J.Got.then(
      Shared.Bytes(),
      Spec.Request,
      J.Framed.read(b),
      t => r => J.Got.then(
        Spec.Body,
        Spec.Request,
        Body.read(r),
        x => r2 => Some{J.Got{Spec.Request{t, x}, r2}}
      )
    )
  )

# one mount's status
def Info.read(b: Shared.Bytes()) -> Maybe<&2, J.Got<Spec.Info>>:
  J.Got.then(
    String,
    Spec.Info,
    J.Utf8.read(b),
    u => r => J.Got.then(
      String,
      Spec.Info,
      J.Utf8.read(r),
      ln => r2 => J.Got.then(
        String,
        Spec.Info,
        J.Utf8.read(r2),
        sp => r3 => J.Got.then(
          Nat,
          Spec.Info,
          J.Leb.read(r3),
          n => r4 => Some{J.Got{Spec.Info{u, ln, sp, n}, r4}}
        )
      )
    )
  )

# n statuses, one after another
def Infos.read.go(n: Nat, b: Shared.Bytes()) -> Maybe<&2, J.Got<List<&2, Spec.Info>>>:
  match n:
    case 0n:
      Some{J.Got{[], b}}
    case 1n+k:
      J.Got.then(
        Spec.Info,
        List<&2, Spec.Info>,
        Info.read(b),
        x => r => J.Got.then(
          List<&2, Spec.Info>,
          List<&2, Spec.Info>,
          Infos.read.go(k, r),
          xs => r2 => Some{J.Got{x <> xs, r2}}
        )
      )

# a response, from its tag
def Response.read(b: Shared.Bytes()) -> Maybe<&2, J.Got<Spec.Response>>:
  match b:
    case Con{0, r}:
      J.Got.then(
        Nat,
        Spec.Response,
        J.Leb.read(r),
        n => r2 => J.Got.then(
          List<&2, Spec.Info>,
          Spec.Response,
          Infos.read.go(n, r2),
          infos => r3 => J.Got.then(
            Nat,
            Spec.Response,
            J.Leb.read(r3),
            c => r4 => Some{J.Got{Spec.StatusIs{infos, c}, r4}}
          )
        )
      )
    case Con{1, r}:
      J.Got.then(
        String,
        Spec.Response,
        J.Utf8.read(r),
        sp => r2 => Some{J.Got{Spec.Mounted{sp}, r2}}
      )
    case Con{2, r}:
      Some{J.Got{Spec.Unmounted{}, r}}
    case Con{3, r}:
      Some{J.Got{Spec.Stopping{}, r}}
    case Con{4, r}:
      J.Got.then(
        String,
        Spec.Response,
        J.Utf8.read(r),
        why => r2 => Some{J.Got{Spec.Denied{why}, r2}}
      )
    case _:
      None{}

def Spec.Response.decode(b):
  Read.whole(Spec.Response, Response.read(b))

# the entry that m read in front of the entries that k reads from the rest
def Entries.read.one(
  m: Maybe<&2, J.Got<Spec.Entry>>,
  k: Shared.Bytes() -> Maybe<&2, List<&2, Spec.Entry>>
) -> Maybe<&2, List<&2, Spec.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{J.Got{e, r}}:
      Maybe.map(&2, List<&2, Spec.Entry>, List<&2, Spec.Entry>, es => e <> es, k(r))

# entries up to the end of the bytes; fuel counts the bytes left
def Entries.read.go(fuel: Nat, b: Shared.Bytes()) -> Maybe<&2, List<&2, Spec.Entry>>:
  match fuel b:
    case _ Nil{}:
      Some{[]}
    case 0n bs:
      None{}
    case 1n+f bs:
      Entries.read.one(
        J.Got.then(
          String,
          Spec.Entry,
          J.Utf8.read(bs),
          u => r => J.Got.then(
            String,
            Spec.Entry,
            J.Utf8.read(r),
            ln => r2 => J.Got.then(
              List<&2, String>,
              Spec.Entry,
              Texts.read(r2),
              gs => r3 => Some{J.Got{Spec.Entry{u, ln, gs}, r3}}
            )
          )
        ),
        r => Entries.read.go(f, r)
      )

def Spec.Entries.decode(b):
  +b = b
  Entries.read.go(List.length(&2, U32, b), b)
