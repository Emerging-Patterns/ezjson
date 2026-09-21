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
