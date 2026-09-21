# ezjson: JSON for Bend 2. `parse` reads text into Maybe Json. `print` writes
# compact text. Build null, booleans, numbers, strings, arrays, and objects;
# read them with get, at, and the typed readers.
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

# an object from pairs
def obj(pairs: List<&1, String & Value.Json>) -> Value.Json:
  Value.obj(pairs)

# an array from a list
def arr(items: List<&2, Value.Json>) -> Value.Json:
  Value.arr(items)

# a non-negative integer
def num(n: U32) -> Value.Json:
  Value.num(n)

# a negative integer; zero stays zero
def neg(n: U32) -> Value.Json:
  Value.neg(n)

# a finite float, in Bend's spelling; infinity and NaN are null
def f32(x: F32) -> Value.Json:
  Value.f32(x)

# a JSON number written as text, or null when the text is not one
def number(raw: String) -> Value.Json:
  Value.number(raw)

# an object's value at a key; JNull when it is not an object or has no such
# key
def get(j: Value.Json, key: String) -> Value.Json:
  Value.get(j, key)

# an array's item at an index; JNull when it is not an array or has none
def at(j: Value.Json, i: U32) -> Value.Json:
  Value.at(j, i)

# a string's text, else the default
def str_or(j: Value.Json, default: String) -> String:
  Value.str_or(j, default)

# a boolean, else the default
def bool_or(j: Value.Json, default: Bool) -> Bool:
  Value.bool_or(j, default)

# a number as a U32, else the default
def u32_or(j: Value.Json, default: U32) -> U32:
  Value.u32_or(j, default)

# a number as an F32, else the default
def f32_or(j: Value.Json, default: F32) -> F32:
  Value.f32_or(j, default)
