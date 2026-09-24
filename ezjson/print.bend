# ezjson/print: a value as compact JSON text.
import Base
import ./value.bend as V

def escape.nib.go(+nn: U32, digit: Bool) -> Char:
  match digit:
    case True{}:
      Char.from_u32(U32.add(48, nn))
    case False{}:
      Char.from_u32(U32.add(87, nn))

def escape.nib(+nn: U32) -> Char:
  escape.nib.go(nn, U32.is_lt(nn, 10))

def escape.u(+cp: U32) -> String:
  "\\u00" ++ String.from_list([escape.nib(U32.div(cp, 16)), escape.nib(U32.mod(cp, 16))])

def escape.rest.go(+cp: U32, ch: Char, ctrl: Bool) -> String:
  match ctrl:
    case True{}:
      escape.u(cp)
    case False{}:
      String.from_list([ch])

def escape.rest(+cp: U32, ch: Char) -> String:
  escape.rest.go(cp, ch, U32.is_lt(cp, 32))

def escape.char(+ch: Char) -> String:
  +x = Char.to_u32(ch)
  Bool.pick(String, U32.is_eq(x, 34), "\\\"",
  Bool.pick(String, U32.is_eq(x, 92), "\\\\",
  Bool.pick(String, U32.is_eq(x, 8), "\\b",
  Bool.pick(String, U32.is_eq(x, 12), "\\f",
  Bool.pick(String, U32.is_eq(x, 10), "\\n",
  Bool.pick(String, U32.is_eq(x, 13), "\\r",
  Bool.pick(String, U32.is_eq(x, 9), "\\t",
    escape.rest(x, ch))))))))

# the chars of a string with quotes, backslashes, and controls escaped
def escape(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      escape.char(c) ++ escape(t)

# a string in quotes, escaped
def quote(txt: String) -> String:
  "\"" ++ escape(String.to_list(txt)) ++ "\""

# a value as compact JSON
def print(val: V.Json) -> String:
  match val:
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
    case V.JSpan{src, +n}:
      quote(V.span.str(src, n, U32.is_zero(n)))
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
    case V.JBind{src, +n, v, V.JNil{}}:
      quote(V.span.str(src, n, U32.is_zero(n))) ++ ":" ++ print(v)
    case V.JBind{src, +n, v, r}:
      quote(V.span.str(src, n, U32.is_zero(n))) ++ ":" ++ print(v) ++ "," ++ print(r)

# a parse result: the value, or "<bad>"
def maybe(mb: Maybe<&2, V.Json>) -> String:
  match mb:
    case None{}:
      "<bad>"
    case Some{j}:
      print(j)
