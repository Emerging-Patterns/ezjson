# ezjson

JSON for [Bend 2](https://github.com/bendlang/bend).

## Install

With [Bend](https://github.com/bendlang/bend) alone there is nothing to
install: import ezjson by its hub name and `bend` fetches it from
[the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first run.
`0x81c67699424929b5c44cd8577e18117f` is ezjson v1.1.0.

```
import 0x81c67699424929b5c44cd8577e18117f/main.bend as Ezjson
```

Or with [ez](https://github.com/Emerging-Patterns/ez), which records the
package in `ez.toml` (`ez init` makes one):

```
ez add Emerging-Patterns/ezjson
```

## Usage

`parse` reads JSON text into `Maybe Json`: null, booleans, numbers, strings,
arrays, and objects. `print` writes that value back as compact text, and
writes U+FFFD for a code point no UTF-8 text can hold (a lone surrogate).
`pretty` writes the same tokens indented two spaces a level, one element or
member a line and a space after each colon, as JavaScript's
`JSON.stringify(v, null, 2)` does, with no newline at the end. A number
keeps the spelling it was parsed with. `num` builds one from that text, and
builds null when the text is not a JSON number. The `Json` type is
`src/value.bend`'s; import that file to name it in a signature, and give a
`match` on a result its own def, since Bend matches only a parameter.

```
import 0x81c67699424929b5c44cd8577e18117f/main.bend as Ezjson
import 0x81c67699424929b5c44cd8577e18117f/src/value.bend as Value

def shown(got: Maybe<&2, Value.Json>) -> String:
  match got:
    case None{}:
      ""
    case Some{j}:
      Ezjson.print(j)

def compact(s: String) -> String:
  shown(Ezjson.parse(s))

def point() -> String:
  Ezjson.print(Ezjson.obj([("x", Ezjson.num("1")), ("y", Ezjson.num("-2")),
    ("name", Ezjson.str("a")), ("ok", Ezjson.bool(True{})),
    ("extra", Ezjson.null())]))
```

`null`, `bool`, `str`, `num`, `arr`, and `obj` build values. `get` reads an
object key and returns the first value when a key is repeated. `at` reads an
array index. `as_bool`, `as_str`, `as_num`, `as_u32`, and `as_f32` read a
value of that kind, or none when the kind differs or the number does not fit.
`has` tells a missing key from a key whose value is null, and `len` counts
the elements of an array or the members of an object.

A multi-gigabyte text is read with a cursor. `parse` builds one tree;
`cursor` does not. `next` returns one event and the cursor after it. `skip`
drops the next value (one scalar, or one array or object and everything
inside it) without building that value. `text` copies the spelling of a
string, a key, or a number. Commas and colons are not events. Import
`src/pull.bend` to name the cursor and match the event constructors.

`cursor` holds the unread suffix of the source. A string or key span
(`Pull.EStrS`, `Pull.EKeyS`) is the first `nn` characters of a suffix, not
a copy. The event holds that suffix, so the span stays readable after
`next` advances, and it is gone when the event is dropped. A number
(`Pull.ENum`) keeps its own spelling, so one number in a big array does
not hold the rest of the array. Dropping the caller's own string variable
does not drop the cursor.

Walk a large object or array one event at a time. `skip` drops a subtree
you do not need. `text` copies an owned string when you need one.

```
import 0x81c67699424929b5c44cd8577e18117f/main.bend as Ezjson
import 0x81c67699424929b5c44cd8577e18117f/src/pull.bend as Pull

def owned.go(step: (Pull.Ev & Pull.Cur)) -> (String & Pull.Cur):
  (ev, rest) = step
  (Maybe.default(&2, String, Ezjson.text(ev), ""), Ezjson.skip(rest))

def owned(cur: Pull.Cur) -> (String & Pull.Cur):
  owned.go(Ezjson.next(cur))
```

## Specification

[SPEC.md](SPEC.md) lists every behavior ezjson guarantees, by ID: conformance
to [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259) and the behavior of
each def in `main.bend`. A row is either proved by a quantified law in
`LAWS.bend`, checked by `bend PROOF.bend` (the first line must be
`All terms check.`), or listed in its trust boundary. A row marked pending is
not guaranteed yet. [docs/rfc/ezjson-spec.md](docs/rfc/ezjson-spec.md) has the
reasoning and the rollout.

`scale/` is a compiled size check that pull-walks large string-row and
nested-array documents without calling `parse`: 32000 string rows
(~563 KiB) and 35000 nested rows of `[0.100,0.200,0.3]` (~615 KiB).
