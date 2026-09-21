# ezjson

JSON for [Bend 2](https://github.com/bendlang/bend). `parse` turns text into
`Maybe Json`. `print` writes compact text. The `Json` type has builders
`obj`, `arr`, and `num`, and accessors `get`, `str_or`, and `u32_or`.
Numbers keep their source text. `ezjson/LAWS.bend` states the library;
`ezjson/PROOF.bend` proves those laws.

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

Import the entry from a clone, or by package hash after `ez publish`:

```
import ./ezjson/main.bend as Ezjson
```

```
import 0x/main.bend as Ezjson
```

## Usage

```
git clone https://github.com/Emerging-Patterns/ezjson
cd ezjson
```

```
import ./ezjson/main.bend as Ezjson

def compact(s: String) -> String:
  match Ezjson.parse(s):
    case None{}:
      ""
    case Some{j}:
      Ezjson.print(j)
```

`Ezjson.obj`, `Ezjson.arr`, and `Ezjson.num` build values. `Ezjson.get`,
`Ezjson.str_or`, and `Ezjson.u32_or` read a missing key or a wrong kind as
the default.
