# ezjson: JSON for Bend 2. `parse` turns text into Maybe Json; `print` writes
# compact text. Build with `obj`, `arr`, and `num`; read with `get`,
# `str_or`, and `u32_or`. Constructors of Json live in ./value.bend.
import Base
import ./value.bend as Value
import ./parse.bend as Parse
import ./print.bend as Print

# a text as a value, or None when it is not JSON
def parse(s: String) -> Maybe<&2, Value.Json>:
  Parse.parse(s)

# a value as compact JSON
def print(j: Value.Json) -> String:
  Print.print(j)

# an object from pairs
def obj(pairs: List<&1, String & Value.Json>) -> Value.Json:
  Value.obj(pairs)

# an array from a list
def arr(items: List<&2, Value.Json>) -> Value.Json:
  Value.arr(items)

# a number
def num(n: U32) -> Value.Json:
  Value.num(n)

# an object's value at a key; JNull when it is not an object or has no such
# key
def get(j: Value.Json, key: String) -> Value.Json:
  Value.get(j, key)

# a string's text, else the default
def str_or(j: Value.Json, default: String) -> String:
  Value.str_or(j, default)

# a number as a U32, else the default
def u32_or(j: Value.Json, default: U32) -> U32:
  Value.u32_or(j, default)
