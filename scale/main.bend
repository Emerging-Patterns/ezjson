# Large fixtures for the pull walker: an object of 32000 string rows
# (~563 KiB) and an object of 35000 nested arrays of `[0.100,0.200,0.3]`
# (~615 KiB). `main` counts those events with the public cursor and skips
# each array. It does not call `parse`.
import Base
import ../main.bend as Ezjson
import ../src/pull.bend as Pull

# push `chunk` onto a reversed buffer
def cat.rev(chunk: String, acc: String) -> String:
  match chunk:
    case SNil{}:
      acc
    case SCon{c, t}:
      cat.rev(t, SCon{c, acc})

# undo a reversed buffer
def flip(txt: String, acc: String) -> String:  # noqa: L001 scale harness, outside the spec
  match txt:
    case SNil{}:
      acc
    case SCon{c, t}:
      flip(t, SCon{c, acc})

# `left` copies of a row, reversed, commas between them. `fresh` is the first
def rows.put(left: Nat, fresh: Bool, acc: String, +one: String, +more: String) -> String:
  match left fresh:
    case 0n b:
      acc
    case 1n+p True{}:
      rows.put(p, False{}, cat.rev(one, acc), one, more)
    case 1n+p False{}:
      rows.put(p, False{}, cat.rev(more, acc), one, more)

# the row text, forwards
def rows.of(nn: Nat, one: String, more: String) -> String:
  flip(rows.put(nn, True{}, "", one, more), "")

# {"rows":[ ... ],"n":1}
def pack(body: String) -> String:  # noqa: L001 scale harness, outside the spec
  "{\"rows\":[" ++ body ++ "],\"n\":1}"

# 32000 string rows
def wide.doc() -> String:
  pack(rows.of(Nat.mul(320n, 100n), "\"0.100,0.200,0.3\"", ",\"0.100,0.200,0.3\""))

# 35000 nested rows
def nest.doc() -> String:
  pack(rows.of(Nat.mul(350n, 100n), "[0.100,0.200,0.3]", ",[0.100,0.200,0.3]"))

# enough steps for one event per character, plus the end
def steps(+src: String) -> Nat:  # noqa: L001 scale harness, outside the spec
  1n+Nat.add(String.length(src), String.length(src))

# the count walk: the next event is still unread, or one is in hand
type Phase is Data:  # noqa: L001 scale harness, outside the spec
  Need{cur: Pull.Cur, acc: U32}
  Have{ev: Pull.Ev, cur: Pull.Cur, acc: U32}

# keep the event just read
def take(acc: U32, got: (Pull.Ev & Pull.Cur)) -> Phase:  # noqa: L001 scale harness, outside the spec
  (ev, cur) = got
  Have{ev, cur, acc}

# one more string-row span
def add.str(ev: Pull.Ev, acc: U32) -> U32:
  match ev:
    case Pull.EStrS{src, nn}:
      U32.add(acc, 1)
    case other:
      acc

# one more number span
def add.num(ev: Pull.Ev, acc: U32) -> U32:
  match ev:
    case Pull.ENum{src, nn}:
      U32.add(acc, 1)
    case other:
      acc

# string spans, or number spans
def add(ev: Pull.Ev, acc: U32, strs: Bool) -> U32:  # noqa: L001 scale harness, outside the spec
  match strs:
    case True{}:
      add.str(ev, acc)
    case False{}:
      add.num(ev, acc)

# count spans until the end. `strs` counts string rows; otherwise numbers
def walk(left: Nat, ph: Phase, +strs: Bool) -> U32:  # noqa: L001 scale harness, outside the spec
  match left ph:
    case n Have{Pull.EEnd{}, cur, acc}:
      acc
    case n Have{Pull.EErr{}, cur, acc}:
      0
    case 0n Have{ev, cur, acc}:
      0
    case 1n+p Have{ev, cur, acc}:
      walk(p, Need{cur, add(ev, acc, strs)}, strs)
    case 0n Need{cur, acc}:
      0
    case 1n+p Need{cur, acc}:
      walk(p, take(acc, Ezjson.next(cur)), strs)

# how many spans `next` yields
def count(+src: String, strs: Bool) -> U32:  # noqa: L001 scale harness, outside the spec
  walk(steps(src), Need{Ezjson.cursor(src), 0}, strs)

# the number after the key that follows a skipped value
def skip.num(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  "#" ++ Maybe.default(&2, String, Ezjson.text(ev), "?")

# that key, then its number
def skip.key(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  "k:" ++ Maybe.default(&2, String, Ezjson.text(ev), "?") ++ skip.num(Ezjson.next(cur))

# skip the value after this key
def skip.val(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  skip.key(Ezjson.next(Ezjson.skip(cur)))

# the key after the object's first key
def skip.mem(got: (Pull.Ev & Pull.Cur)) -> String:
  (ev, cur) = got
  skip.val(Ezjson.next(cur))

# skip the array and read the next member
def skipped(src: String) -> String:  # noqa: L001 scale harness, outside the spec
  skip.mem(Ezjson.next(Ezjson.cursor(src)))

# the count and the member after the skipped array
def report(+src: String, strs: Bool, label: String) -> String:  # noqa: L001 scale harness, outside the spec
  U32.show(count(src, strs)) ++ " " ++ label ++ skipped(src)

def main() -> String:  # noqa: L001 entry point
  "rows=" ++ report(wide.doc(), True{}, "skip-rows=")
    ++ " nest=" ++ report(nest.doc(), False{}, "skip-nest=")
