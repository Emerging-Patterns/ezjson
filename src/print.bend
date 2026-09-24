# src/print: a value as compact or indented JSON text.
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

# whether a code point is a Unicode scalar value: not a surrogate, and not
# past U+10FFFF. No UTF-8 JSON text can hold any other
def scalar(+cp: U32) -> Bool:
  Bool.not(Bool.or(Bool.and(U32.is_ge(cp, 55296), U32.is_le(cp, 57343)), U32.is_gt(cp, 1114111)))

# one scalar value, escaped when JSON requires it
def escape.plain(+cp: U32, ch: Char) -> String:
  Bool.pick(String, U32.is_eq(cp, 34), "\\\"",
  Bool.pick(String, U32.is_eq(cp, 92), "\\\\",
  Bool.pick(String, U32.is_eq(cp, 8), "\\b",
  Bool.pick(String, U32.is_eq(cp, 12), "\\f",
  Bool.pick(String, U32.is_eq(cp, 10), "\\n",
  Bool.pick(String, U32.is_eq(cp, 13), "\\r",
  Bool.pick(String, U32.is_eq(cp, 9), "\\t",
    escape.rest(cp, ch))))))))

# a scalar value as escape.plain writes it; any other code point as U+FFFD,
# as Go's encoding/json writes invalid UTF-8
def escape.scalar(+cp: U32, ch: Char, ok: Bool) -> String:
  match ok:
    case True{}:
      escape.plain(cp, ch)
    case False{}:
      String.from_list([Char.from_u32(65533)])

# one char of a string
def escape.char(+ch: Char) -> String:
  +cp = Char.to_u32(ch)
  escape.scalar(cp, ch, scalar(cp))

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

# a value as indented JSON. `pad` is the spaces a value's lines start with,
# after their newline. For a chain of cells, a newline and `pad` start each
# element or member, and `close` follows the last one, before the bracket
def pretty.go(val: V.Json, +pad: String, +close: String) -> String:
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
    case V.JArr{V.JNil{}}:
      "[]"
    case V.JArr{items}:
      +inner = "  " ++ pad
      "[\n" ++ inner ++ pretty.go(items, inner, "\n" ++ pad) ++ "]"
    case V.JObj{V.JNil{}}:
      "{}"
    case V.JObj{pairs}:
      +inner = "  " ++ pad
      "{\n" ++ inner ++ pretty.go(pairs, inner, "\n" ++ pad) ++ "}"
    case V.JNil{}:
      ""
    case V.JCons{h, V.JNil{}}:
      pretty.go(h, pad, "") ++ close
    case V.JCons{h, t}:
      pretty.go(h, pad, "") ++ ",\n" ++ pad ++ pretty.go(t, pad, close)
    case V.JPair{k, v, V.JNil{}}:
      quote(k) ++ ": " ++ pretty.go(v, pad, "") ++ close
    case V.JPair{k, v, r}:
      quote(k) ++ ": " ++ pretty.go(v, pad, "") ++ ",\n" ++ pad ++ pretty.go(r, pad, close)
    case V.JBind{src, +n, v, V.JNil{}}:
      quote(V.span.str(src, n, U32.is_zero(n))) ++ ": " ++ pretty.go(v, pad, "") ++ close
    case V.JBind{src, +n, v, r}:
      quote(V.span.str(src, n, U32.is_zero(n))) ++ ": " ++ pretty.go(v, pad, "") ++ ",\n" ++ pad ++
        pretty.go(r, pad, close)

# a value as JSON indented two spaces a level, one element or member a line
def pretty(val: V.Json) -> String:
  pretty.go(val, "", "")

# a parse result: the value, or "<bad>"
def maybe(mb: Maybe<&2, V.Json>) -> String:
  match mb:
    case None{}:
      "<bad>"
    case Some{j}:
      print(j)
