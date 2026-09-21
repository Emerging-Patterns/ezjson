# ezjson/value: a JSON value. Arrays and objects hold their cells inside the
# type (JCons, JPair, JNil) rather than in a List, so every traversal is a
# structural recursion on one argument -- which Bend's termination checker
# accepts, and which keeps laws provable. Build and read them through the
# defs below, never by hand.
import Base
import ./lazy.bend as Lazy

# a JSON value; JNil, JCons and JPair are the cells of arrays and objects
type Json is Data:
  JNull{}
  JBool{b: Bool}
  JNum{raw: String}
  JStr{s: String}
  JArr{items: Json}
  JObj{pairs: Json}
  JNil{}
  JCons{head: Json, tail: Json}
  JPair{key: String, val: Json, rest: Json}

# reverses a chain of JCons or JPair cells onto acc
def reverse(cells: Json, acc: Json) -> Json:
  match cells:
    case JCons{h, t}:
      reverse(t, JCons{h, acc})
    case JPair{k, v, r}:
      reverse(r, JPair{k, v, acc})
    case _:
      acc

# builders
def arr.go(items: List<&2, Json>) -> Json:
  match items:
    case Nil{}:
      JNil{}
    case Con{h, t}:
      JCons{h, arr.go(t)}

# an array from a list
def arr(items: List<&2, Json>) -> Json:
  JArr{arr.go(items)}

def obj.go(pairs: List<&1, String & Json>) -> Json:
  match pairs:
    case Nil{}:
      JNil{}
    case Con{(k, v), t}:
      JPair{k, v, obj.go(t)}

# an object from pairs
def obj(pairs: List<&1, String & Json>) -> Json:
  JObj{obj.go(pairs)}

# a number
def num(n: U32) -> Json:
  JNum{U32.show(n)}

# accessors: a missing key or a wrong kind reads as JNull / None / the default,
# so paths chain: get(get(msg, "params"), "textDocument")
def find(cells: Json, +key: String) -> Json:
  match cells:
    case JPair{+k, v, r}:
      Lazy.stop(Json, String.eq(k, key), v, _u => find(r, key))
    case other:
      JNull{}

# an object's value at a key; JNull when it is not an object or has no such
# key
def get(j: Json, key: String) -> Json:
  match j:
    case JObj{pairs}:
      find(pairs, key)
    case other:
      JNull{}

# a string's text, else the default
def str_or(j: Json, default: String) -> String:
  match j:
    case JStr{s}:
      s
    case other:
      default

# a number as a U32, else the default
def u32_or(j: Json, default: U32) -> U32:
  match j:
    case JNum{raw}:
      Maybe.default(&2, U32, U32.read(raw), default)
    case other:
      default

# an array's first item
def first(j: Json) -> Json:
  match j:
    case JArr{JCons{h, t}}:
      h
    case other:
      JNull{}
