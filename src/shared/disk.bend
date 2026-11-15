import Base

# Disk
# ----
# The effects of a program that keeps its state in files: steps that may
# fail with a message, files read and written whole as bytes, words kept as
# bytes, the directories and the removal of files that Base has no effect
# for, done by the programs of the operating system (mkdir, ls, rm), and
# messages over TCP. This is code that runs and talks to the operating
# system: no law covers it.

# Steps that may fail
# -------------------

# an effect that answers a value of A, or a message that says why it could not
def Run(-A: Type) -> Type:
  IO(Result<&1, &1, String, A>)

# the step that answers x
def Run.pure(-A: Type, x: A) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, Done{x})

# what f does with the value of r; a message of r stays
def Run.next(-A: Type, -B: Type, r: Result<&1, &1, String, A>, f: A -> Run(B)) -> Run(B):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, String, B>, Fail{e})
    case Done{x}:
      f(x)

# the step m, then f on its value
def Run.bind(-A: Type, -B: Type, m: Run(A), f: A -> Run(B)) -> Run(B):
  IO.bind(Result<&1, &1, String, A>, Result<&1, &1, String, B>, m, r => Run.next(A, B, r, f))

# the step that fails with the message msg
def Run.fail(-A: Type, msg: String) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, Fail{msg})

# the step that answers what r holds
def Run.of(-A: Type, r: Result<&1, &1, String, A>) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, r)

# the effect m, as a step that does not fail
def Run.io(-A: Type, m: IO(A)) -> Run(A):
  IO.bind(A, Result<&1, &1, String, A>, m, x => IO.pure(Result<&1, &1, String, A>, Done{x}))

# what the effect answered, with what it was doing (what) before its message
def Run.sys.of(
  -A: Type,
  what: String,
  r: Result<&1, &1, U32 & String, A>
) -> Result<&1, &1, String, A>:
  match r:
    case Fail{(code, msg)}:
      Fail{what ++ ": " ++ msg}
    case Done{x}:
      Done{x}

# the effect m of Base, as a step whose message says what it was doing
def Run.sys(-A: Type, what: String, m: IO(Result<&1, &1, U32 & String, A>)) -> Run(A):
  IO.bind(
    Result<&1, &1, U32 & String, A>,
    Result<&1, &1, String, A>,
    m,
    r => IO.pure(Result<&1, &1, String, A>, Run.sys.of(A, what, r))
  )

# what r holds, with the message msg for its message
def Run.else.of(-A: Type, msg: String, r: Result<&1, &1, String, A>) -> Result<&1, &1, String, A>:
  match r:
    case Fail{e}:
      Fail{msg}
    case Done{x}:
      Done{x}

# the step m, which fails with the message msg when it fails
def Run.else(-A: Type, msg: String, m: Run(A)) -> Run(A):
  IO.bind(
    Result<&1, &1, String, A>,
    Result<&1, &1, String, A>,
    m,
    r => IO.pure(Result<&1, &1, String, A>, Run.else.of(A, msg, r))
  )

# Words as bytes
# --------------
# A word is kept as its four bytes, the highest first.

# the bytes of the words ws, then rest
def Words.bytes(ws: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      rest
    case Con{+w, more}:
      +hi = (w / 65536: U32)
      b0 = (hi / 256: U32)
      b0
        <> (hi % 256: U32)
        <> ((w / 256: U32) % 256: U32)
        <> (w % 256: U32)
        <> Words.bytes(more, rest)

# the words of the bytes bs, after the words acc in reverse order; none when
# the bytes do not end at a whole word
def Words.of_bytes(bs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case Con{a, Con{b, Con{c, Con{d, rest}}}}:
      Words.of_bytes(rest, (((a * 256 + b: U32) * 256 + c: U32) * 256 + d: U32) <> acc)
    case _:
      None{}

# Words as short bytes
# --------------------
# A word kept in as few bytes as it needs (LEB128): seven bits to a byte, the
# lowest first, and the highest bit set on each byte but the last of a word.
# A word below 128 (a count, a tag, an ASCII byte) is one byte; a word of a
# SHA-256 at most five. Every UTF-8 form of a word below 0x110000 is as long
# or longer, and a word of four bytes is longer for each word below 2^28.

# the k lowest groups of seven bits of the word w, the lowest first, each but
# the last with its highest bit set, then rest
def Short.put(k: Nat, +w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      rest
    case 1n+m:
      +m = m
      more = Bool.to_u32(Bool.not(Nat.is_eq(m, 0n)))
      (w % 128 + more * 128: U32) <> Short.put(m, (w / 128: U32), rest)

# how many bytes the word w takes
def Short.size(+w: U32) -> Nat:
  Bool.pick(
    Nat,
    (w < 128: U32),
    1n,
    Bool.pick(
      Nat,
      (w < 16384: U32),
      2n,
      Bool.pick(Nat, (w < 2097152: U32), 3n, Bool.pick(Nat, (w < 268435456: U32), 4n, 5n))
    )
  )

# the short bytes of the words ws, then rest
def Short.bytes(ws: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      rest
    case Con{+w, more}:
      Short.put(Short.size(w), w, Short.bytes(more, rest))

# the words of the short bytes bs, after the words out in reverse order and
# the part acc of a word whose next group of seven bits has the value mul;
# none when the bytes end inside a word
def Short.read(
  bs: List<&2, U32>,
  acc: U32,
  +mul: U32,
  out: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        U32.is_eq(mul, 1),
        Some{List.reverse(&2, U32, out)},
        None{}
      )
    case Con{+b, rest}:
      +x = (acc + (b % 128: U32) * mul: U32)
      +last = (b < 128: U32)
      Short.read(
        rest,
        Bool.pick(U32, last, 0, x),
        Bool.pick(U32, last, 1, (mul * 128: U32)),
        List.filter.put(U32, x, out, last)
      )

# the words of the short bytes bs; none when they end inside a word
def Short.words(bs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Short.read(bs, 0, 1, [])

# Files
# -----

# what the effect on a file answered, and the file closed
def File.done(
  -A: Type,
  p: File & Result<&1, &1, U32 & String, A>
) -> IO(Result<&1, &1, U32 & String, A>):
  (f, r) = p
  IO.bind(
    Unit,
    Result<&1, &1, U32 & String, A>,
    File.close(f),
    u => IO.pure(Result<&1, &1, U32 & String, A>, r)
  )

# the bytes of the file whose size p answered, and the file closed
def File.sized(
  p: File & Result<&1, &1, U32 & String, U32>
) -> IO(Result<&1, &1, U32 & String, List<&2, U32>>):
  match p:
    case (f, Fail{e}):
      do IO<Result<&1, &1, U32 & String, List<&2, U32>>>:
        File.close(f)
        return Fail{e}
    case (f, Done{size}):
      IO.bind(
        File & Result<&1, &1, U32 & String, List<&2, U32>>,
        Result<&1, &1, U32 & String, List<&2, U32>>,
        File.read_bytes(f, size),
        File.done(List<&2, U32>)
      )

# the bytes of the file at the path path
def Disk.read(+path: String) -> Run(List<&2, U32>):
  do Run<List<&2, U32>>:
    f: File <- Run.sys(File, "open " ++ path, File.open(path, "r"))
    Run.sys(
      List<&2, U32>,
      "read " ++ path,
      IO.bind(
        File & Result<&1, &1, U32 & String, U32>,
        Result<&1, &1, U32 & String, List<&2, U32>>,
        File.size(f),
        File.sized
      )
    )

# the file at the path path, opened in the mode mode of File.open, after it
# took the bytes bs
def Disk.write(+path: String, mode: String, bs: List<&2, U32>) -> Run(Unit):
  do Run<Unit>:
    f: File <- Run.sys(File, "open " ++ path, File.open(path, mode))
    Run.sys(
      Unit,
      "write " ++ path,
      IO.bind(
        File & Result<&1, &1, U32 & String, Unit>,
        Result<&1, &1, U32 & String, Unit>,
        File.write_bytes(f, bs),
        File.done(Unit)
      )
    )

# the words m that the file at the path path holds, if it ends at a whole word
def Words.got(path: String, m: Maybe<&2, List<&2, U32>>) -> Run(List<&2, U32>):
  match m:
    case None{}:
      Run.fail(List<&2, U32>, path ++ ": the file does not end at a whole word")
    case Some{ws}:
      Run.pure(List<&2, U32>, ws)

# the words of the file at the path path
def Disk.words(+path: String) -> Run(List<&2, U32>):
  do Run<List<&2, U32>>:
    bs: List<&2, U32> <- Disk.read(path)
    Words.got(path, Words.of_bytes(bs, []))

# the words of the file at the path path, kept as short bytes
def Disk.shorts(+path: String) -> Run(List<&2, U32>):
  do Run<List<&2, U32>>:
    bs: List<&2, U32> <- Disk.read(path)
    Words.got(path, Short.words(bs))

# Programs
# --------

# what the program answered: its output when its status is 0, else what it
# said on its error output
def Program.done(r: U32 & (String & String)) -> Result<&1, &1, String, String>:
  match r:
    case (0, (out, err)):
      Done{out}
    case (status, (out, err)):
      Fail{err}

# the output of the program program run with the arguments args
def Program.run(+program: String, args: List<String>) -> Run(String):
  Run.bind(
    U32 & (String & String),
    String,
    Run.sys(U32 & (String & String), program, Process.run(program, args, "", 67108864, 60000)),
    r => Run.of(String, Program.done(r))
  )

# a new directory at the path path; it fails when the path is there
def Disk.make_dir(path: String) -> Run(Unit):
  do Run<Unit>:
    out: String <- Program.run("mkdir", [path])
    return Unit{}

# the names in the directory at the path path
def Disk.names(path: String) -> Run(List<&2, String>):
  do Run<List<&2, String>>:
    out: String <- Program.run("ls", ["-1", path])
    return List.filter(~String, ~(s => Bool.not(String.is_empty(s))), String.lines(out))

# the files at the paths paths removed; a path that is not there is no error
def Disk.remove(paths: List<String>) -> Run(Unit):
  do Run<Unit>:
    out: String <- Program.run("rm", "-f" <> paths)
    return Unit{}

# Messages over TCP
# -----------------
# A message is its length in bytes, as four bytes, the highest first, then
# its bytes. A socket is a handle that each step hands on, so a step on a
# socket answers the socket beside its result.

# a step on a socket that answers a value of A, or a message that says why it
# could not, with the socket
def Sock(-A: Type) -> Type:
  IO(Socket & Result<&1, &1, String, A>)

# the step on the socket s that answers x
def Sock.pure(-A: Type, s: Socket, x: A) -> Sock(A):
  IO.pure(Socket & Result<&1, &1, String, A>, (s, Done{x}))

# what f does with the socket and the value of p; a message of p stays
def Sock.next(
  -A: Type,
  -B: Type,
  p: Socket & Result<&1, &1, String, A>,
  f: Socket -> A -> Sock(B)
) -> Sock(B):
  match p:
    case (s, Fail{e}):
      IO.pure(Socket & Result<&1, &1, String, B>, (s, Fail{e}))
    case (s, Done{x}):
      f(s)(x)

# the step m, then f on its socket and value
def Sock.bind(-A: Type, -B: Type, m: Sock(A), f: Socket -> A -> Sock(B)) -> Sock(B):
  IO.bind(
    Socket & Result<&1, &1, String, A>,
    Socket & Result<&1, &1, String, B>,
    m,
    p => Sock.next(A, B, p, f)
  )

# what a step on a socket answered, and the socket closed
def Sock.closed(-A: Type, p: Socket & Result<&1, &1, String, A>) -> Run(A):
  (s, r) = p
  IO.bind(
    Unit,
    Result<&1, &1, String, A>,
    Socket.close(s),
    u => IO.pure(Result<&1, &1, String, A>, r)
  )

# the step on a socket m, as a step that closes the socket once it is done
def Sock.close(-A: Type, m: Sock(A)) -> Run(A):
  IO.bind(Socket & Result<&1, &1, String, A>, Result<&1, &1, String, A>, m, p => Sock.closed(A, p))

# what a send answered, as a step on its socket
def Net.sent(
  what: String,
  p: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>
) -> Sock(Unit):
  match p:
    case (s, Fail{((code, msg), rest)}):
      IO.pure(Socket & Result<&1, &1, String, Unit>, (s, Fail{what ++ ": " ++ msg}))
    case (s, Done{u}):
      IO.pure(Socket & Result<&1, &1, String, Unit>, (s, Done{u}))

# the bytes bs sent on the socket s as one message
def Net.send(s: Socket, +bs: List<&2, U32>) -> Sock(Unit):
  n = U32.from_nat(List.length(&2, U32, bs))
  IO.bind(
    Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>,
    Socket & Result<&1, &1, String, Unit>,
    TCP.send_bytes(s, Words.bytes([n], bs)),
    p => Net.sent("send", p)
  )

# f on both sides of the pair p
def Pair.on(-A: Type, -B: Type, -C: Type, p: A & B, f: A -> B -> C) -> C:
  (a, b) = p
  f(a)(b)

# what f does with the socket t and the bytes that a receive on it answered
# (r); it fails when none came in time, or the connection closed
def Net.got(
  t: Socket,
  r: Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit>,
  f: Socket -> List<&2, U32> -> Sock(List<&2, U32>)
) -> Sock(List<&2, U32>):
  match r:
    case Wait{u}:
      IO.pure(
        Socket & Result<&1, &1, String, List<&2, U32>>,
        (t, Fail{"receive: the other node sent nothing in time"})
      )
    case Ready{Fail{(code, msg)}}:
      IO.pure(Socket & Result<&1, &1, String, List<&2, U32>>, (t, Fail{"receive: " ++ msg}))
    case Ready{Done{None{}}}:
      IO.pure(
        Socket & Result<&1, &1, String, List<&2, U32>>,
        (t, Fail{"receive: the other node closed the connection"})
      )
    case Ready{Done{Some{bs}}}:
      f(t)(bs)

# n bytes from the socket s after the chunks acc in reverse order, unless
# they all came (done), in at most k receives that each wait at most ms
# milliseconds
def Net.recv.go(
  k: Nat,
  done: Bool,
  +ms: U32,
  +n: U32,
  acc: List<&2, List<&2, U32>>,
  s: Socket
) -> Sock(List<&2, U32>):
  match k done:
    case _ True{}:
      Sock.pure(List<&2, U32>, s, List.concat(&2, U32, List.reverse(&2, List<&2, U32>, acc)))
    case 0n False{}:
      IO.pure(
        Socket & Result<&1, &1, String, List<&2, U32>>,
        (s, Fail{"receive: the message is too long"})
      )
    case 1n+j False{}:
      IO.bind(
        Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit>,
        Socket & Result<&1, &1, String, List<&2, U32>>,
        TCP.try_recv_bytes(s, n, ms),
        q => Pair.on(
          Socket,
          Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit>,
          Sock(List<&2, U32>),
          q,
          t => r => Net.got(
            t,
            r,
            t2 => +bs => Net.recv.go(
              j,
              U32.is_eq(n, U32.from_nat(List.length(&2, U32, bs))),
              ms,
              (n - U32.from_nat(List.length(&2, U32, bs)): U32),
              bs <> acc,
              t2
            )
          )
        )
      )

# n bytes from the socket s, each receive waiting at most ms milliseconds
def Net.recv.some(s: Socket, +n: U32, ms: U32) -> Sock(List<&2, U32>):
  Net.recv.go(1048576n, U32.is_eq(n, 0), ms, n, [], s)

# the length that the four bytes m give, if they are four
def Net.length(m: List<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      Some{(((a * 256 + b: U32) * 256 + c: U32) * 256 + d: U32)}
    case _:
      None{}

# the bytes of the message whose length m gives, from the socket s
def Net.body(s: Socket, m: Maybe<&2, U32>, ms: U32) -> Sock(List<&2, U32>):
  match m:
    case None{}:
      IO.pure(Socket & Result<&1, &1, String, List<&2, U32>>, (s, Fail{"receive: no length"}))
    case Some{n}:
      Net.recv.some(s, n, ms)

# the bytes of one message from the socket s, each receive waiting at most ms
# milliseconds
def Net.recv(s: Socket, +ms: U32) -> Sock(List<&2, U32>):
  Sock.bind(
    List<&2, U32>,
    List<&2, U32>,
    Net.recv.some(s, 4, ms),
    t => bs => Net.body(t, Net.length(bs), ms)
  )
