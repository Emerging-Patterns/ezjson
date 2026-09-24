# serde_json vs ezjson bench driver. JSON text fixtures on disk feed the CLI;
# speed paths load once then time parse/print, or a pull walk, only (IO.now).
# Native ELF via `bend bench/main.bend -o …` (CC=clang -O3 in the flake).
import ../main.bend as Ezjson
import ../src/value.bend as V
import ../src/pull.bend as Pull

# unwrap a parsed U32, or zero when parse fails
def u32.arg.go(mb: Maybe<&2, U32>) -> U32:
  match mb:
    case Some{n}:
      n
    case None{}:
      0

# parse a decimal U32 from a string
def u32.arg(txt: String) -> U32:
  u32.arg.go(U32.read(txt))

# close the file once the write Result is Unit
def wrote.close(file: File, ok: Unit) -> IO(Unit):
  match ok:
    case Unit{}:
      File.close(file)

# force a write Result, then close the file
def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):  # noqa: L001 IO driver
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
def took.after(txt: String, closed: Unit) -> String:
  match closed:
    case Unit{}:
      txt

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
def write.maybe(path: String, mb: Maybe<&2, V.Json>) -> IO(Unit):
  match mb:
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
def cmd.json.rt.go(dst: String, mb: Maybe<&2, V.Json>) -> IO(Unit):
  match mb:
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
def json.sum(val: V.Json, +acc: U32) -> U32:
  match val:
    case V.JNull{}:
      (acc + 1 : U32)
    case V.JBool{True{}}:
      (acc + 2 : U32)
    case V.JBool{False{}}:
      (acc + 3 : U32)
    case V.JNum{raw}:
      (acc + U32.from_nat(String.length(raw)) + 4 : U32)
    case V.JStr{s}:
      (acc + U32.from_nat(String.length(s)) + 5 : U32)
    case V.JSpan{_src, +n}:
      (acc + n + 5 : U32)
    case V.JArr{items}:
      json.sum(items, (acc + 6 : U32))
    case V.JObj{pairs}:
      json.sum(pairs, (acc + 7 : U32))
    case V.JNil{}:
      acc
    case V.JCons{h, t}:
      json.sum(t, json.sum(h, acc))
    case V.JPair{k, v, r}:
      json.sum(r, json.sum(v, (acc + U32.from_nat(String.length(k)) : U32)))
    case V.JBind{_src, +n, v, r}:
      json.sum(r, json.sum(v, (acc + n : U32)))

# fold a successful parse into the checksum
def step.dec(+sum: U32, mb: Maybe<&2, V.Json>) -> U32:
  match mb:
    case None{}:
      sum
    case Some{j}:
      json.sum(j, (sum + 1 : U32))

# repeat parse n times
def loop.dec(+txt: String, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.dec(txt, p, step.dec(sum, Ezjson.parse(txt)))

# fold print length into a checksum
def step.enc(+sum: U32, out: String) -> U32:
  (sum + U32.from_nat(String.length(out)) + 1 : U32)

# repeat print n times
def loop.enc(+val: V.Json, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.enc(val, p, step.enc(sum, Ezjson.print(val)))

# format a timing line for the harness
def show.ms(t0: Nat, t1: Nat, +sum: U32, +bytes: U32, +nn: U32) -> String:
  "MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " BY "
    ++ U32.show(bytes) ++ " N " ++ U32.show(nn)

# timed decode body once the text is loaded
def bench.json.dec.go(+txt: String, nn: Nat, +iters: U32) -> IO(Unit):
  +bytes = U32.from_nat(String.length(txt))
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.dec(txt, nn, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, bytes, iters))

# timed decode: load text outside IO.now, parse N times inside
def bench.json.dec(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    s : String <- read.text(path)
    bench.json.dec.go(s, k, nn)

# timed encode from a parsed fixture (load+parse outside the timer)
def bench.json.enc.go(mb: Maybe<&2, V.Json>, +nn: U32, +bytes: U32) -> IO(Unit):
  match mb:
    case None{}:
      die.msg("bad json for bench-json-enc")
    case Some{+j}:
      +k = U32.to_nat(nn)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.enc(j, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, bytes, nn))

# after loading text, parse once then time print
def bench.json.enc.after(+txt: String, +nn: U32) -> IO(Unit):
  bench.json.enc.go(Ezjson.parse(txt), nn, U32.from_nat(String.length(txt)))

# load JSON text, parse once, then time print only
def bench.json.enc(path: String, +nn: U32) -> IO(Unit):
  do IO<Unit>:
    s : String <- read.text(path)
    bench.json.enc.after(s, nn)

# checksum tag of one pull event. Same numbers as the Rust token walk:
# null 1, bool 2, number 3, string 4, key 5, begin-array 6, end-array 7,
# begin-object 8, end-object 9, end 10, error 11. A skipped value is 12.
# Spans are not copied here.
def ev.tag(ev: Pull.Ev) -> U32:
  match ev:
    case Pull.ENull{}:
      1
    case Pull.EBool{_b}:
      2
    case Pull.ENum{_src, _nn}:
      3
    case Pull.EStr{_body}:
      4
    case Pull.EStrS{_src, _nn}:
      4
    case Pull.EKey{_body}:
      5
    case Pull.EKeyS{_src, _nn}:
      5
    case Pull.EBeginArr{}:
      6
    case Pull.EEndArr{}:
      7
    case Pull.EBeginObj{}:
      8
    case Pull.EEndObj{}:
      9
    case Pull.EEnd{}:
      10
    case Pull.EErr{}:
      11

# whether this key is the name `rows`
def key.rows(body: String) -> Bool:
  String.eq(body, "rows")

# whether this key span is `rows`, without copying it
def key.rows.span(+src: String, +nn: U32) -> Bool:
  V.span.eq(src, nn, "rows")

# add one walk's checksum into the running total
def step.pull(+sum: U32, part: U32) -> U32:
  (sum + part : U32)

# char length of a copied string, or zero when `text` has none
def text.n(mb: Maybe<&2, String>) -> U32:
  match mb:
    case None{}:
      0
    case Some{s}:
      U32.from_nat(String.length(s))

# a direct `rows` element is due: depth 1 and the countdown is 1
def row.sample(+depth: U32, +every: U32) -> Bool:
  Bool.and(U32.is_eq(depth, 1), U32.is_eq(every, 1))

# decrement only while a string is a direct `rows` element
def countdown.go(inside: Bool, +every: U32) -> U32:
  match inside:
    case True{}:
      U32.sub(every, 1)
    case False{}:
      every

# steps until the next copied row; unchanged outside `rows`
def countdown(+depth: U32, +every: U32) -> U32:  # noqa: L001 bench harness, outside the spec
  countdown.go(U32.is_eq(depth, 1), every)

# full `next` walk. Fuel is the Nat; `AGo` already counted its event
type All is Data:  # noqa: L001 bench harness, outside the spec
  ANeed{cur: Pull.Cur, acc: U32}
  AGo{cur: Pull.Cur, acc: U32}
  AStop{acc: U32}

# the next read
def all.need(cur: Pull.Cur, +acc: U32) -> All:
  ANeed{cur, acc}

# end of a walk. The cursor is dropped
def all.stop(_cur: Pull.Cur, +acc: U32) -> All:
  AStop{acc}

# classify one event. End and error stop; anything else keeps walking
def all.have.ev(ev: Pull.Ev, cur: Pull.Cur, +acc: U32) -> All:
  match ev:
    case Pull.EEnd{}:
      all.stop(cur, (acc + 10 : U32))
    case Pull.EErr{}:
      all.stop(cur, (acc + 11 : U32))
    case other:
      AGo{cur, (acc + ev.tag(other) : U32)}

# the event `next` just returned
def all.have(+acc: U32, got: (Pull.Ev & Pull.Cur)) -> All:
  (ev, cur) = got
  all.have.ev(ev, cur, acc)

# one full event walk. `left` shrinks on every self-call
def walk.all(left: Nat, ph: All) -> U32:
  match left ph:
    case 0n AStop{+acc}:
      acc
    case 0n ANeed{_cur, +acc}:
      acc
    case 0n AGo{_cur, +acc}:
      acc
    case 1n+p AStop{+acc}:
      acc
    case 1n+p ANeed{cur, +acc}:
      walk.all(p, all.have(acc, Ezjson.next(cur)))
    case 1n+p AGo{cur, +acc}:
      walk.all(p, all.need(cur, acc))

# `next` until end, `nn` times
def loop.pull.walk(+txt: String, nn: Nat, +sum: U32, +fuel: Nat) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.pull.walk(txt, p, step.pull(sum, walk.all(fuel, all.need(Ezjson.cursor(txt), 0))), fuel)

# skip-walk. `KKey` is the bool "this key is rows"
type Sk is Data:  # noqa: L001 bench harness, outside the spec
  KNeed{cur: Pull.Cur, acc: U32}
  KGo{cur: Pull.Cur, acc: U32}
  KStop{acc: U32}
  KKey{rows: Bool, cur: Pull.Cur, acc: U32}

# the next read
def skip.need(cur: Pull.Cur, +acc: U32) -> Sk:
  KNeed{cur, acc}

# end of a skip-walk
def skip.stop(_cur: Pull.Cur, +acc: U32) -> Sk:
  KStop{acc}

# a key, with whether it names `rows`
def skip.key(rows: Bool, cur: Pull.Cur, +acc: U32) -> Sk:
  KKey{rows, cur, acc}

# classify one event. A `rows` key becomes KKey; other events keep walking
def skip.have.ev(ev: Pull.Ev, cur: Pull.Cur, +acc: U32) -> Sk:
  match ev:
    case Pull.EEnd{}:
      skip.stop(cur, (acc + 10 : U32))
    case Pull.EErr{}:
      skip.stop(cur, (acc + 11 : U32))
    case Pull.EKey{body}:
      skip.key(key.rows(body), cur, (acc + 5 : U32))
    case Pull.EKeyS{src, nn}:
      skip.key(key.rows.span(src, nn), cur, (acc + 5 : U32))
    case other:
      KGo{cur, (acc + ev.tag(other) : U32)}

# the event `next` just returned
def skip.have(+acc: U32, got: (Pull.Ev & Pull.Cur)) -> Sk:
  (ev, cur) = got
  skip.have.ev(ev, cur, acc)

# walk, but `skip` the value named `rows`. `left` shrinks on every self-call
def walk.skip(left: Nat, ph: Sk) -> U32:
  match left ph:
    case 0n KStop{+acc}:
      acc
    case 0n KNeed{_cur, +acc}:
      acc
    case 0n KGo{_cur, +acc}:
      acc
    case 0n KKey{_rows, _cur, +acc}:
      acc
    case 1n+p KStop{+acc}:
      acc
    case 1n+p KNeed{cur, +acc}:
      walk.skip(p, skip.have(acc, Ezjson.next(cur)))
    case 1n+p KGo{cur, +acc}:
      walk.skip(p, skip.need(cur, acc))
    case 1n+p KKey{True{}, cur, +acc}:
      walk.skip(p, skip.need(Ezjson.skip(cur), (acc + 12 : U32)))
    case 1n+p KKey{False{}, cur, +acc}:
      walk.skip(p, skip.need(cur, acc))

# skip-walk, `nn` times
def loop.pull.skip(+txt: String, nn: Nat, +sum: U32, +fuel: Nat) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.pull.skip(txt, p, step.pull(sum, walk.skip(fuel, skip.need(Ezjson.cursor(txt), 0))), fuel)

# text-walk. `arm` means the next value is the `rows` array.
# `depth` 1 is a direct element of that array. `every` counts down to a copy
type Txt is Data:  # noqa: L001 bench harness, outside the spec
  TNeed{cur: Pull.Cur, acc: U32, depth: U32, every: U32, arm: Bool}
  TStop{acc: U32}

# the next read, carrying the row state
def txt.need(cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32, arm: Bool) -> Txt:
  TNeed{cur, acc, depth, every, arm}

# end of a text-walk
def txt.stop(_cur: Pull.Cur, +acc: U32) -> Txt:
  TStop{acc}

# inside `rows`, go one level deeper; otherwise stay outside
def txt.nest.go(zero: Bool, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  match zero:
    case True{}:
      txt.need(cur, acc, 0, every, False{})
    case False{}:
      txt.need(cur, acc, (depth + 1 : U32), every, False{})

# open a container that is not the `rows` array itself
def txt.nest(cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.nest.go(U32.is_zero(depth), cur, acc, depth, every)

# step out of a container. Depth 0 stays 0
def txt.close.go(zero: Bool, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  match zero:
    case True{}:
      txt.need(cur, acc, 0, every, False{})
    case False{}:
      txt.need(cur, acc, U32.sub(depth, 1), every, False{})

# close one array or object
def txt.close(cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.close.go(U32.is_zero(depth), cur, acc, depth, every)

# `rows` array: its elements are depth 1 and the first is copied
def txt.arr.go(arm: Bool, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  match arm:
    case True{}:
      txt.need(cur, acc, 1, 1, False{})
    case False{}:
      txt.nest(cur, acc, depth, every)

# begin-array. `arm` is set when the key was `rows`
def txt.arr(arm: Bool, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.arr.go(arm, cur, acc, depth, every)

# copy this owned string and restart the countdown at 8
def txt.own.yes(body: String, cur: Pull.Cur, +acc: U32, +depth: U32, _every: U32) -> Txt:
  txt.need(cur, (acc + 4 + text.n(Ezjson.text(Pull.EStr{body})) : U32), depth, 8, False{})

# count an owned string without copying it
def txt.own.no(_body: String, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.need(cur, (acc + 4 : U32), depth, countdown(depth, every), False{})

# owned string: copy it only when it is a sampled row
def txt.own.at(sample: Bool, body: String, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  match sample:
    case True{}:
      txt.own.yes(body, cur, acc, depth, every)
    case False{}:
      txt.own.no(body, cur, acc, depth, every)

# an owned string event
def txt.own(body: String, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.own.at(row.sample(depth, every), body, cur, acc, depth, every)

# copy this span with `text` and restart the countdown at 8
def txt.spn.yes(src: String, +nn: U32, cur: Pull.Cur, +acc: U32, +depth: U32, _every: U32) -> Txt:
  txt.need(cur, (acc + 4 + text.n(Ezjson.text(Pull.EStrS{src, nn})) : U32), depth, 8, False{})

# count a span without copying it
def txt.spn.no(_src: String, _nn: U32, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.need(cur, (acc + 4 : U32), depth, countdown(depth, every), False{})

# span string: `text` copies it only when it is a sampled row
def txt.spn.at(sample: Bool, src: String, +nn: U32, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  match sample:
    case True{}:
      txt.spn.yes(src, nn, cur, acc, depth, every)
    case False{}:
      txt.spn.no(src, nn, cur, acc, depth, every)

# a span string event
def txt.spn(src: String, +nn: U32, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32) -> Txt:
  txt.spn.at(row.sample(depth, every), src, nn, cur, acc, depth, every)

# one event, as the next text-walk state
def txt.classify(ev: Pull.Ev, cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32, arm: Bool) -> Txt:
  match ev:
    case Pull.EEnd{}:
      txt.stop(cur, (acc + 10 : U32))
    case Pull.EErr{}:
      txt.stop(cur, (acc + 11 : U32))
    case Pull.ENull{}:
      txt.need(cur, (acc + 1 : U32), depth, every, False{})
    case Pull.EBool{_b}:
      txt.need(cur, (acc + 2 : U32), depth, every, False{})
    case Pull.ENum{_src, _nn}:
      txt.need(cur, (acc + 3 : U32), depth, every, False{})
    case Pull.EBeginObj{}:
      txt.nest(cur, (acc + 8 : U32), depth, every)
    case Pull.EEndObj{}:
      txt.close(cur, (acc + 9 : U32), depth, every)
    case Pull.EBeginArr{}:
      txt.arr(arm, cur, (acc + 6 : U32), depth, every)
    case Pull.EEndArr{}:
      txt.close(cur, (acc + 7 : U32), depth, every)
    case Pull.EKey{body}:
      txt.need(cur, (acc + 5 : U32), depth, every, key.rows(body))
    case Pull.EKeyS{src, nn}:
      txt.need(cur, (acc + 5 : U32), depth, every, key.rows.span(src, nn))
    case Pull.EStr{body}:
      txt.own(body, cur, acc, depth, every)
    case Pull.EStrS{src, nn}:
      txt.spn(src, nn, cur, acc, depth, every)

# unpack one `next`
def txt.got(+acc: U32, +depth: U32, +every: U32, arm: Bool, got: (Pull.Ev & Pull.Cur)) -> Txt:
  (ev, cur) = got
  txt.classify(ev, cur, acc, depth, every, arm)

# read one event and classify it
def txt.read(cur: Pull.Cur, +acc: U32, +depth: U32, +every: U32, arm: Bool) -> Txt:
  txt.got(acc, depth, every, arm, Ezjson.next(cur))

# full walk, plus `text` on every 8th direct string of each `rows` array.
# `left` shrinks once per event
def walk.text(left: Nat, ph: Txt) -> U32:
  match left ph:
    case 0n TStop{+acc}:
      acc
    case 0n TNeed{_cur, +acc, _depth, _every, _arm}:
      acc
    case 1n+p TStop{+acc}:
      acc
    case 1n+p TNeed{cur, +acc, +depth, +every, arm}:
      walk.text(p, txt.read(cur, acc, depth, every, arm))

# text-walk, `nn` times
def loop.pull.text(+sv: String, nn: Nat, +sum: U32, +fuel: Nat) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.pull.text(sv, p, step.pull(sum, walk.text(fuel, txt.need(Ezjson.cursor(sv), 0, 0, 0, False{}))), fuel)

# two events of fuel per character, plus the end event. Built once, outside the timer
def fuel.nat(+bytes: U32) -> Nat:
  16n+Nat.add(U32.to_nat(bytes), U32.to_nat(bytes))

# print one timed pull loop. The text is already loaded
def bench.pull.show(+bytes: U32, +iters: U32, t0: Nat, t1: Nat, +sum: U32) -> IO(Unit):
  IO.print(show.ms(t0, t1, sum, bytes, iters))

# time a full `next` walk. Load stays outside IO.now
def bench.pull.walk.go(+txt: String, nn: Nat, +iters: U32) -> IO(Unit):
  +bytes = U32.from_nat(String.length(txt))
  +fuel = fuel.nat(bytes)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.pull.walk(txt, nn, 0, fuel)
    t1 : Nat <- IO.now()
    bench.pull.show(bytes, iters, t0, t1, sum)

# load the text, then time the full event walk
def bench.pull.walk(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    s : String <- read.text(path)
    bench.pull.walk.go(s, k, nn)

# time a walk that skips each `rows` array
def bench.pull.skip.go(+txt: String, nn: Nat, +iters: U32) -> IO(Unit):
  +bytes = U32.from_nat(String.length(txt))
  +fuel = fuel.nat(bytes)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.pull.skip(txt, nn, 0, fuel)
    t1 : Nat <- IO.now()
    bench.pull.show(bytes, iters, t0, t1, sum)

# load the text, then time skip of each heavy `rows` array
def bench.pull.skip(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    s : String <- read.text(path)
    bench.pull.skip.go(s, k, nn)

# time a walk that copies every 8th `rows` string with `text`
def bench.pull.text.go(+txt: String, nn: Nat, +iters: U32) -> IO(Unit):
  +bytes = U32.from_nat(String.length(txt))
  +fuel = fuel.nat(bytes)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.pull.text(txt, nn, 0, fuel)
    t1 : Nat <- IO.now()
    bench.pull.show(bytes, iters, t0, t1, sum)

# load the text, then time `text` on a subset of string rows
def bench.pull.text(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    s : String <- read.text(path)
    bench.pull.text.go(s, k, nn)

# fallthrough for unknown commands
def run.f.at(hit: Bool, +cmd: String, _a: String, _b: String, _c: String) -> IO(Unit):
  match hit:
    case True{}:
      IO.print("pong")
    case False{}:
      die.msg("unknown command " ++ cmd)

# dispatch the ping command
def run.f(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.f.at(String.eq(cmd, "ping"), cmd, arg1, arg2, arg3)

# dispatch bench-pull-text
def run.i.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      bench.pull.text(arg1, u32.arg(arg2))
    case False{}:
      run.f(cmd, arg1, arg2, arg3)

# try bench-pull-text then fall through
def run.i(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.i.at(String.eq(cmd, "bench-pull-text"), cmd, arg1, arg2, arg3)

# dispatch bench-pull-skip
def run.h.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      bench.pull.skip(arg1, u32.arg(arg2))
    case False{}:
      run.i(cmd, arg1, arg2, arg3)

# try bench-pull-skip then fall through
def run.h(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.h.at(String.eq(cmd, "bench-pull-skip"), cmd, arg1, arg2, arg3)

# dispatch bench-pull-walk
def run.g.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      bench.pull.walk(arg1, u32.arg(arg2))
    case False{}:
      run.h(cmd, arg1, arg2, arg3)

# try bench-pull-walk then fall through
def run.g(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.g.at(String.eq(cmd, "bench-pull-walk"), cmd, arg1, arg2, arg3)

# dispatch bench-json-enc
def run.e.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      bench.json.enc(arg1, u32.arg(arg2))
    case False{}:
      run.g(cmd, arg1, arg2, arg3)

# try bench-json-enc then fall through
def run.e(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.e.at(String.eq(cmd, "bench-json-enc"), cmd, arg1, arg2, arg3)

# dispatch bench-json-dec
def run.d.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      bench.json.dec(arg1, u32.arg(arg2))
    case False{}:
      run.e(cmd, arg1, arg2, arg3)

# try bench-json-dec then fall through
def run.d(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.d.at(String.eq(cmd, "bench-json-dec"), cmd, arg1, arg2, arg3)

# dispatch json-rt
def run.c.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      cmd.json.rt(arg1, arg2)
    case False{}:
      run.d(cmd, arg1, arg2, arg3)

# try json-rt then fall through
def run.c(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.c.at(String.eq(cmd, "json-rt"), cmd, arg1, arg2, arg3)

# dispatch json-enc
def run.b.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      cmd.json.enc(arg1, arg2)
    case False{}:
      run.c(cmd, arg1, arg2, arg3)

# try json-enc then fall through
def run.b(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "json-enc"), cmd, arg1, arg2, arg3)

# dispatch json-dec
def run.named.at(hit: Bool, +cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  match hit:
    case True{}:
      cmd.json.dec(arg1, arg2)
    case False{}:
      run.b(cmd, arg1, arg2, arg3)

# try json-dec then fall through
def run.named(+cmd: String, +arg1: String, +arg2: String, +arg3: String) -> IO(Unit):
  run.named.at(String.eq(cmd, "json-dec"), cmd, arg1, arg2, arg3)

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
def main() -> IO(Unit):  # noqa: L001 IO entry point
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.of4(args))
