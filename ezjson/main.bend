# ezjson: JSON for Bend 2. `parse` reads text into Maybe Json. `print` writes
# compact text. Build null, booleans, numbers, strings, arrays, and objects;
# read them with get, at, and as_bool, as_str, as_num, as_u32, as_f32.
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

# null
def null() -> Value.Json:
  Value.null()

# a boolean
def bool(b: Bool) -> Value.Json:
  Value.bool(b)

# a string
def str(s: String) -> Value.Json:
  Value.str(s)

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
def get(j: Value.Json, key: String) -> Value.Json:
  Value.get(j, key)

# an array's item at an index; JNull when it is not an array or has none
def at(j: Value.Json, i: U32) -> Value.Json:
  Value.at(j, i)

# a boolean, or none when the value is not one
def as_bool(j: Value.Json) -> Maybe<&2, Bool>:
  Value.as_bool(j)

# a string, or none when the value is not one
def as_str(j: Value.Json) -> Maybe<&2, String>:
  Value.as_str(j)

# a number's text, or none when the value is not a number
def as_num(j: Value.Json) -> Maybe<&2, String>:
  Value.as_num(j)

# a number as a U32, or none when it is not one or does not fit
def as_u32(j: Value.Json) -> Maybe<&2, U32>:
  Value.as_u32(j)

# a number as an F32, or none when it is not one or does not fit
def as_f32(j: Value.Json) -> Maybe<&2, F32>:
  Value.as_f32(j)
