# ezjson

JSON for [Bend 2](https://github.com/bendlang/bend). `parse` reads text into
`Maybe Json` (null, booleans, numbers, strings, arrays, objects). `print`
writes compact text. Build with `null`, `bool`, `str`, `num`, `arr`, and
`obj`; read with `get`, `at`, and `as_*`. Laws and proofs live in
`ezjson/LAWS.bend` and `ezjson/PROOF.bend`.

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
