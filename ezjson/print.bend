# ezjson/print: a value as compact JSON text.
import Base
import ./value.bend as V

def escape.nib.go(+n: U32, digit: Bool) -> Char:
  match digit:
    case True{}:
      Char.from_u32(U32.add(48, n))
    case False{}:
      Char.from_u32(U32.add(87, n))

def escape.nib(+n: U32) -> Char:
  escape.nib.go(n, U32.is_lt(n, 10))

def escape.u(+x: U32) -> String:
  "\\u00" ++ String.from_list([escape.nib(U32.div(x, 16)), escape.nib(U32.mod(x, 16))])

def escape.rest.go(+x: U32, c: Char, ctrl: Bool) -> String:
  match ctrl:
    case True{}:
      escape.u(x)
    case False{}:
      String.from_list([c])

def escape.rest(+x: U32, c: Char) -> String:
  escape.rest.go(x, c, U32.is_lt(x, 32))

def escape.char(+c: Char) -> String:
  +x = Char.to_u32(c)
  Bool.pick(String, U32.is_eq(x, 34), "\\\"",
  Bool.pick(String, U32.is_eq(x, 92), "\\\\",
  Bool.pick(String, U32.is_eq(x, 8), "\\b",
  Bool.pick(String, U32.is_eq(x, 12), "\\f",
  Bool.pick(String, U32.is_eq(x, 10), "\\n",
  Bool.pick(String, U32.is_eq(x, 13), "\\r",
  Bool.pick(String, U32.is_eq(x, 9), "\\t",
    escape.rest(x, c))))))))

# the chars of a string with quotes, backslashes, and controls escaped
def escape(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      escape.char(c) ++ escape(t)

# a string in quotes, escaped
def quote(s: String) -> String:
  "\"" ++ escape(String.to_list(s)) ++ "\""

# a value as compact JSON
def print(j: V.Json) -> String:
  match j:
    case V.JNull{}:
      "null"
    case V.JBool{True{}}:
      "true"
    case V.JBool{False{}}:
      "false"
    case V.JNum{raw}:
      raw
    case V.JStr{s}:
      quote(s)
    case V.JArr{items}:
      "[" ++ print(items) ++ "]"
    case V.JObj{pairs}:
      "{" ++ print(pairs) ++ "}"
    case V.JNil{}:
      ""
    case V.JCons{h, V.JNil{}}:
      print(h)
    case V.JCons{h, t}:
      print(h) ++ "," ++ print(t)
    case V.JPair{k, v, V.JNil{}}:
      quote(k) ++ ":" ++ print(v)
    case V.JPair{k, v, r}:
      quote(k) ++ ":" ++ print(v) ++ "," ++ print(r)

# a parse result: the value, or "<bad>"
def maybe(m: Maybe<&2, V.Json>) -> String:
  match m:
    case None{}:
      "<bad>"
    case Some{j}:
      print(j)
