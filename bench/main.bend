# serde_json vs ezjson bench driver. JSON text fixtures on disk feed the CLI;
# speed paths load once then time parse/print only (IO.now). Native ELF via
# `bend bench/main.bend -o …` (CC=clang -O3 in the flake derivation).
import ../ezjson/main.bend as Ezjson
import ../ezjson/value.bend as V

# unwrap a parsed U32, or zero when parse fails
def u32.arg.go(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{n}:
      n
    case None{}:
      0

# parse a decimal U32 from a string
def u32.arg(s: String) -> U32:
  u32.arg.go(U32.read(s))

# close the file once the write Result is Unit
def wrote.close(file: File, ok: Unit) -> IO(Unit):
  match ok:
    case Unit{}:
      File.close(file)

# force a write Result, then close the file
def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (file, result) = pair
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, result)
    wrote.close(file, ok)

# write a String to a path
def write.text(path: String, data: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, data)
    wrote(p)

# after reading text, close the file and return it
def took.after(s: String, closed: Unit) -> String:
  match closed:
    case Unit{}:
      s

# force a read Result, then close the file
def took.text(pair: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (file, result) = pair
  do IO<String>:
    s : String <- IO.pass(String, result)
    closed : Unit <- File.close(file)
    return took.after(s, closed)

# read n chars after learning the file size
def read.n(pair: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  (file, result) = pair
  do IO<String>:
    n : U32 <- IO.pass(U32, result)
    p : File & Result<&1, &1, U32 & String, String> <- File.read(file, n)
    took.text(p)

# read a whole file as text (UTF-8 → String)
def read.text(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read.n(p)

# die with a message
def die.msg(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

# write printed JSON, or die on parse failure
def write.maybe(path: String, m: Maybe<&2, V.Json>) -> IO(Unit):
  match m:
    case None{}:
      die.msg("parse failed")
    case Some{j}:
      write.text(path, Ezjson.print(j))

# decode: parse JSON text → compact print
def cmd.json.dec(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read.text(src)
    write.maybe(dst, Ezjson.parse(s))

# encode: parse once then print (value → compact text)
def cmd.json.enc(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read.text(src)
    write.maybe(dst, Ezjson.parse(s))

# round-trip: parse → print → parse → print
def cmd.json.rt.go(dst: String, m: Maybe<&2, V.Json>) -> IO(Unit):
  match m:
    case None{}:
      die.msg("round-trip parse failed")
    case Some{j}:
      write.maybe(dst, Ezjson.parse(Ezjson.print(j)))

# JSON round-trip from text to text
def cmd.json.rt(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    s : String <- read.text(src)
    cmd.json.rt.go(dst, Ezjson.parse(s))

# fold a Json tree into a checksum so timed work is not DCE'd
def json.sum(j: V.Json, +a: U32) -> U32:
  match j:
    case V.JNull{}:
      (a + 1 : U32)
    case V.JBool{True{}}:
      (a + 2 : U32)
    case V.JBool{False{}}:
      (a + 3 : U32)
    case V.JNum{raw}:
      (a + U32.from_nat(String.length(raw)) + 4 : U32)
    case V.JStr{s}:
      (a + U32.from_nat(String.length(s)) + 5 : U32)
    case V.JSpan{_src, +n}:
      (a + n + 5 : U32)
    case V.JArr{items}:
      json.sum(items, (a + 6 : U32))
    case V.JObj{pairs}:
      json.sum(pairs, (a + 7 : U32))
    case V.JNil{}:
      a
    case V.JCons{h, t}:
      json.sum(t, json.sum(h, a))
    case V.JPair{k, v, r}:
      json.sum(r, json.sum(v, (a + U32.from_nat(String.length(k)) : U32)))
    case V.JBind{_src, +n, v, r}:
      json.sum(r, json.sum(v, (a + n : U32)))

# fold a successful parse into the checksum
def step.dec(+sum: U32, m: Maybe<&2, V.Json>) -> U32:
  match m:
    case None{}:
      sum
    case Some{j}:
      json.sum(j, (sum + 1 : U32))

# repeat parse n times
def loop.dec(+s: String, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.dec(s, p, step.dec(sum, Ezjson.parse(s)))

# fold print length into a checksum
def step.enc(+sum: U32, out: String) -> U32:
  (sum + U32.from_nat(String.length(out)) + 1 : U32)

# repeat print n times
def loop.enc(+j: V.Json, n: Nat, +sum: U32) -> U32:
  match n:
    case 0n:
      sum
    case 1n+p:
      loop.enc(j, p, step.enc(sum, Ezjson.print(j)))

# format a timing line for the harness
def show.ms(t0: Nat, t1: Nat, +sum: U32, +bytes: U32, +n: U32) -> String:
  "MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " BY "
    ++ U32.show(bytes) ++ " N " ++ U32.show(n)

# timed decode: load text outside IO.now, parse N times inside
def bench.json.dec(path: String, +n: U32) -> IO(Unit):
  +k = U32.to_nat(n)
  do IO<Unit>:
    s : String <- read.text(path)
    +bytes = U32.from_nat(String.length(s))
    t0 : Nat <- IO.now()
    sum : U32 = loop.dec(s, k, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, bytes, n))

# timed encode from a parsed fixture (load+parse outside the timer)
def bench.json.enc.go(m: Maybe<&2, V.Json>, +n: U32, +bytes: U32) -> IO(Unit):
  match m:
    case None{}:
      die.msg("bad json for bench-json-enc")
    case Some{+j}:
      +k = U32.to_nat(n)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.enc(j, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, bytes, n))

# load JSON text, parse once, then time print only
def bench.json.enc(path: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    s : String <- read.text(path)
    bench.json.enc.go(Ezjson.parse(s), n, U32.from_nat(String.length(s)))

# fallthrough for unknown commands
def run.f.at(z: Bool, +cmd: String, _a: String, _b: String, _c: String) -> IO(Unit):
  match z:
    case True{}:
      IO.print("pong")
    case False{}:
      die.msg("unknown command " ++ cmd)

# dispatch the ping command
def run.f(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.f.at(String.eq(cmd, "ping"), cmd, a, b, c)

# dispatch bench-json-enc
def run.e.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.json.enc(a, u32.arg(b))
    case False{}:
      run.f(cmd, a, b, c)

# try bench-json-enc then fall through
def run.e(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.e.at(String.eq(cmd, "bench-json-enc"), cmd, a, b, c)

# dispatch bench-json-dec
def run.d.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      bench.json.dec(a, u32.arg(b))
    case False{}:
      run.e(cmd, a, b, c)

# try bench-json-dec then fall through
def run.d(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.d.at(String.eq(cmd, "bench-json-dec"), cmd, a, b, c)

# dispatch json-rt
def run.c.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.json.rt(a, b)
    case False{}:
      run.d(cmd, a, b, c)

# try json-rt then fall through
def run.c(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.c.at(String.eq(cmd, "json-rt"), cmd, a, b, c)

# dispatch json-enc
def run.b.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.json.enc(a, b)
    case False{}:
      run.c(cmd, a, b, c)

# try json-enc then fall through
def run.b(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "json-enc"), cmd, a, b, c)

# dispatch json-dec
def run.named.at(z: Bool, +cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match z:
    case True{}:
      cmd.json.dec(a, b)
    case False{}:
      run.b(cmd, a, b, c)

# try json-dec then fall through
def run.named(+cmd: String, +a: String, +b: String, +c: String) -> IO(Unit):
  run.named.at(String.eq(cmd, "json-dec"), cmd, a, b, c)

# the first four argv strings, empty when missing
def args.of4(xs: List<String>) -> String & String & String & String:
  match xs:
    case a <> b <> c <> d <> _t:
      (a, b, c, d)
    case a <> b <> c <> Nil{}:
      (a, b, c, "")
    case a <> b <> Nil{}:
      (a, b, "", "")
    case a <> Nil{}:
      (a, "", "", "")
    case Nil{}:
      ("", "", "", "")

# unpack argv and run the named command
def main.go(quad: String & String & String & String) -> IO(Unit):
  (a, b, c, d) = quad
  run.named(a, b, c, d)

# CLI entry: dispatch by the first argv word
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.of4(args))
