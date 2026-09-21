# ezjson

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import 0xa3c2445eb44c5d8406e6229be518fccb/main.bend as Ezjson
```

## Usage

`parse` reads JSON text into `Maybe Json`: null, booleans, numbers, strings,
arrays, and objects. `print` writes that value back as compact text. A number
keeps the spelling it was parsed with. `num` builds a non-negative integer,
`neg` a negative integer (`neg(0)` is `0`), `f32` a finite float in Bend's
spelling, and `number` any other JSON number text.

```
import 0xa3c2445eb44c5d8406e6229be518fccb/main.bend as Ezjson

def compact(s: String) -> String:
  match Ezjson.parse(s):
    case None{}:
      ""
    case Some{j}:
      Ezjson.print(j)

def point() -> String:
  Ezjson.print(Ezjson.obj([("x", Ezjson.num(1)), ("y", Ezjson.neg(2)),
    ("name", Ezjson.str("a")), ("ok", Ezjson.bool(True{})),
    ("extra", Ezjson.null())]))
```

`null`, `bool`, `str`, `num`, `neg`, `f32`, `number`, `arr`, and `obj` build
values. `get` reads an object key and returns the first value when a key is
repeated. `at` reads an array index. `str_or`, `bool_or`, `u32_or`, and
`f32_or` read a value of that kind, or the default when the kind differs or
the number does not fit.
