# ezjson

JSON for [Bend 2](https://github.com/bendlang/bend).

## Install

Use with [Bend](https://github.com/bendlang/bend) or install easily with [ez](https://github.com/Emerging-Patterns/ez):

```
ez init
ez add Emerging-Patterns/ezjson
```

## Usage

`parse` reads JSON text into `Maybe Json`: null, booleans, numbers, strings,
arrays, and objects. `print` writes that value back as compact text. A number
keeps the spelling it was parsed with. `num` builds one from that text, and
builds null when the text is not a JSON number.

```
import 0xa3c2445eb44c5d8406e6229be518fccb/main.bend as Ezjson

def compact(s: String) -> String:
  match Ezjson.parse(s):
    case None{}:
      ""
    case Some{j}:
      Ezjson.print(j)

def point() -> String:
  Ezjson.print(Ezjson.obj([("x", Ezjson.num("1")), ("y", Ezjson.num("-2")),
    ("name", Ezjson.str("a")), ("ok", Ezjson.bool(True{})),
    ("extra", Ezjson.null())]))
```

`null`, `bool`, `str`, `num`, `arr`, and `obj` build values. `get` reads an
object key and returns the first value when a key is repeated. `at` reads an
array index. `as_bool`, `as_str`, `as_num`, `as_u32`, and `as_f32` read a
value of that kind, or none when the kind differs or the number does not fit.

A multi-gigabyte text is read with a cursor. `parse` builds one tree;
`cursor` does not. `next` returns one event and the cursor after it. `skip`
drops the next value (one scalar, or one array or object and everything
inside it) without building that value. `text` copies the spelling of a
string, a key, or a number. Commas and colons are not events. Import
`pull.bend` to match the event constructors.

`cursor` holds the unread suffix of the source. A span (`Pull.EStrS`,
`Pull.EKeyS`, `Pull.ENum`) is the first `nn` characters of a suffix, not a
copy. The event holds that suffix, so the span stays readable after `next`
advances, and it is gone when the event is dropped. Dropping the caller's
own string variable does not drop the cursor.

A `laya-weights-json-v2` pack is one object whose matrices are arrays of
string rows. Walk it like this: `next` yields the object, then a key, then
the array; each following `next` is one row (`EStrS` when the row has no
escapes, `EStr` when it does). `text` copies a row only when an owned
`String` is needed. `skip`, called after a key and before the value, drops
a matrix the loader does not want. After `skip` of one array element the
comma stays, so the next `next` reads the following element. After `skip`
of a whole array the cursor sits just past `]`.

```
import 0xa3c2445eb44c5d8406e6229be518fccb/main.bend as Ezjson
import 0xa3c2445eb44c5d8406e6229be518fccb/pull.bend as Pull

def row(cur: Pull.Cur) -> String:
  (ev, _rest) = Ezjson.next(cur)
  Maybe.default(&2, String, Ezjson.text(ev), "")
```

## Compliance

Closed equalities in `ezjson/LAWS.bend`, proved in `ezjson/PROOF.bend`
(`bend ezjson/PROOF.bend`), check these parts of
[RFC 8259](https://www.rfc-editor.org/rfc/rfc8259):

- §2: insignificant whitespace is only space, tab, line feed, and carriage
  return, and a text holds one value.
- §3: `null`, `true`, `false`, a number, a string, an array, and an object
  parse as those kinds. The literals are lowercase.
- §4 and §5: `{}` and `[]` are values, a member name is a string, and a
  trailing comma is rejected.
- §6: a number keeps its spelling. `NaN`, `Infinity`, a leading `+`, and a
  leading zero are rejected.
- §7: a raw U+0000–U+001F in a string is rejected. `\u0000`–`\u001F` and the
  short escapes decode. A lone surrogate is rejected, and a surrogate pair
  is one code point.
- §8.1: a leading U+FEFF is rejected, and `print` does not emit one.
- §8.3: an escape and the same character unescaped compare equal, including
  an object name.
- §10: `print` escapes U+0000–U+001F.

The same sections hold for the cursor. `pull_atoms`, `pull_nums`,
`pull_text`, `pull_ws`, `pull_one`, `pull_bad`, and `pull_struct` read
those values one event at a time. `pull_skip` drops a value.
`pull_span`, `pull_rows`, and `pull_rows_skip` walk a weight-pack object
of 64 string rows as events, not as one `parse` tree. `pull_steps` counts
the events of a 24-number array (begin, each number, end, and done).
`public_cursor`, `public_next`, `public_skip`, and `public_text` are the
wrappers in `main.bend`.

`scale/main.bend` is the size check. After ezjson 0.2.0, `parse` of a
string-row embed loads at 24k rows (~447 KiB) and overflows the stack at
28k (~523 KiB). A nested embed loads at 16k (~295 KiB) and is killed at
32k (~599 KiB). The scale program does not call `parse`. It builds a
string-row pack of 32000 rows (~563 KiB) and a nested pack of 35000 rows
of `[0.100,0.200,0.3]` (~615 KiB), counts them with `next`, and `skip`s
each row array. Both sit past those failure points.
