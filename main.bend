# ezjson: JSON for Bend 2, with a parser, a printer and a pull cursor
#
# `parse` reads text into Maybe Json. `print` writes compact text and
# `pretty` indented text. `cursor` reads one event at a time. Build null,
# booleans, numbers, strings, arrays, and objects; read them with get, at, and
# as_bool, as_str, as_num, as_u32, as_f32; has and len tell a missing key or
# index from a null.
import Base
import ./src/value.bend as Value
import ./src/parse.bend as Parse
import ./src/print.bend as Print
import ./src/pull.bend as Pull

# a text as a value, or None when it is not JSON
def parse(txt: String) -> Maybe<&2, Value.Json>:
  Parse.parse(txt)

# a value as compact JSON
def print(val: Value.Json) -> String:
  Print.print(val)

# a value as JSON indented two spaces a level, one element or member a line,
# with no newline at the end
def pretty(val: Value.Json) -> String:
  Print.pretty(val)

# null
def null() -> Value.Json:
  Value.null()

# a boolean
def bool(flag: Bool) -> Value.Json:
  Value.bool(flag)

# a string
def str(txt: String) -> Value.Json:
  Value.str(txt)

# a JSON number from its text, or null when that text is not one
def num(raw: String) -> Value.Json:
  Value.num(raw)

# an object from pairs
def obj(pairs: List<&1, String & Value.Json>) -> Value.Json:
  Value.obj(pairs)

# an array from a list
def arr(items: List<&2, Value.Json>) -> Value.Json:
  Value.arr(items)

# an object's value at a key; JNull when it is not an object or has no such
# key
def get(val: Value.Json, key: String) -> Value.Json:
  Value.get(val, key)

# an array's item at an index; JNull when it is not an array or has none
def at(val: Value.Json, idx: U32) -> Value.Json:
  Value.at(val, idx)

# whether an object has a key; false when the value is not an object. Tells
# a missing key from a key whose value is null, which `get` does not
def has(val: Value.Json, key: String) -> Bool:
  Value.has(val, key)

# how many elements an array, or members an object, has; 0 for anything else
def len(val: Value.Json) -> U32:
  Value.len(val)

# a boolean, or none when the value is not one
def as_bool(val: Value.Json) -> Maybe<&2, Bool>:
  Value.as_bool(val)

# a string, or none when the value is not one
def as_str(val: Value.Json) -> Maybe<&2, String>:
  Value.as_str(val)

# a number's text, or none when the value is not a number
def as_num(val: Value.Json) -> Maybe<&2, String>:
  Value.as_num(val)

# a number as a U32, or none when it is not one or does not fit
def as_u32(val: Value.Json) -> Maybe<&2, U32>:
  Value.as_u32(val)

# a number as an F32, or none when it is not one or does not fit
def as_f32(val: Value.Json) -> Maybe<&2, F32>:
  Value.as_f32(val)

# a cursor at the start of a JSON text. It holds the unread suffix of that
# text. A span event keeps its own suffix, so it stays valid after `next`
# moves the cursor, and it is gone when the event is dropped
def cursor(src: String) -> Pull.Cur:
  Pull.cursor(src)

# the next event. Commas and colons are not events. After the root value,
# the next call is the end, or an error if another value follows
def next(cur: Pull.Cur) -> (Pull.Ev & Pull.Cur):
  Pull.next(cur)

# drop the next value, scalar or container, without building it
def skip(cur: Pull.Cur) -> Pull.Cur:
  Pull.skip(cur)

# the text of a string, key, or number event, copying a span. None otherwise
def text(ev: Pull.Ev) -> Maybe<&2, String>:
  Pull.text(ev)
