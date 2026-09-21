# ezjson/value: a JSON value. Null, bool, number, string, array, and object.
# An array is a JArr of JCons cells ending in JNil; an object is a JObj of
# JPair cells ending in JNil. A number keeps its source text.
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

# where a scan of a JSON number is
type Num is Data:
  NStart{}
  NInt{}
  NZero{}
  NDig{}
  NDot{}
  NFrac{}
  NExp{}
  NExpN{}
  NExpD{}
  NBad{}

# reverses a chain of JCons or JPair cells onto acc
def reverse(cells: Json, acc: Json) -> Json:
  match cells:
    case JCons{h, t}:
      reverse(t, JCons{h, acc})
    case JPair{k, v, r}:
      reverse(r, JPair{k, v, acc})
    case _:
      acc

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

# null
def null() -> Json:
  JNull{}

# a boolean
def bool(b: Bool) -> Json:
  JBool{b}

# a string
def str(s: String) -> Json:
  JStr{s}

# a non-negative integer
def num(n: U32) -> Json:
  JNum{U32.show(n)}

def neg.go(z: Bool, n: U32) -> Json:
  match z:
    case True{}:
      JNum{"0"}
    case False{}:
      JNum{"-" ++ U32.show(n)}

# a negative integer; zero stays zero
def neg(+n: U32) -> Json:
  neg.go(U32.is_zero(n), n)

def number.go(raw: String, ok: Bool) -> Json:
  match ok:
    case True{}:
      JNum{raw}
    case False{}:
      JNull{}

def number.ok.digit(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def number.ok.expmark(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 101), U32.is_eq(x, 69))

def number.ok.lead(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 49), U32.is_le(x, 57))

def number.ok.step.lead(ok: Bool) -> Num:
  match ok:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def number.ok.step.int.go(+x: U32, zero: Bool) -> Num:
  match zero:
    case True{}:
      NZero{}
    case False{}:
      number.ok.step.lead(number.ok.lead(x))

def number.ok.step.int(+x: U32) -> Num:
  number.ok.step.int.go(x, U32.is_eq(x, 48))

def number.ok.step.start.go(+x: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NInt{}
    case False{}:
      number.ok.step.int(x)

def number.ok.step.start(+x: U32) -> Num:
  number.ok.step.start.go(x, U32.is_eq(x, 45))

def number.ok.step.mark.go(mark: Bool) -> Num:
  match mark:
    case True{}:
      NExp{}
    case False{}:
      NBad{}

def number.ok.step.mark(+x: U32) -> Num:
  number.ok.step.mark.go(number.ok.expmark(x))

def number.ok.step.body.digit(more: Bool) -> Num:
  match more:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def number.ok.step.body.other.go(+x: U32, dot: Bool) -> Num:
  match dot:
    case True{}:
      NDot{}
    case False{}:
      number.ok.step.mark(x)

def number.ok.step.body.other(+x: U32) -> Num:
  number.ok.step.body.other.go(x, U32.is_eq(x, 46))

def number.ok.step.body.go(+x: U32, more: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      number.ok.step.body.digit(more)
    case False{}:
      number.ok.step.body.other(x)

def number.ok.step.body(+x: U32, more: Bool) -> Num:
  number.ok.step.body.go(x, more, number.ok.digit(x))

def number.ok.step.frac.other(+x: U32, have: Bool) -> Num:
  match have:
    case True{}:
      number.ok.step.mark(x)
    case False{}:
      NBad{}

def number.ok.step.frac.go(+x: U32, have: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      NFrac{}
    case False{}:
      number.ok.step.frac.other(x, have)

def number.ok.step.frac(+x: U32, have: Bool) -> Num:
  number.ok.step.frac.go(x, have, number.ok.digit(x))

def number.ok.step.expd.go(digit: Bool) -> Num:
  match digit:
    case True{}:
      NExpD{}
    case False{}:
      NBad{}

def number.ok.step.expd(+x: U32) -> Num:
  number.ok.step.expd.go(number.ok.digit(x))

def number.ok.step.exps.minus.go(+x: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NExpN{}
    case False{}:
      number.ok.step.expd(x)

def number.ok.step.exps.minus(+x: U32) -> Num:
  number.ok.step.exps.minus.go(x, U32.is_eq(x, 45))

def number.ok.step.exps.go(+x: U32, plus: Bool) -> Num:
  match plus:
    case True{}:
      NExpN{}
    case False{}:
      number.ok.step.exps.minus(x)

def number.ok.step.exps(+x: U32) -> Num:
  number.ok.step.exps.go(x, U32.is_eq(x, 43))

def number.ok.step(st: Num, +x: U32) -> Num:
  match st:
    case NStart{}:
      number.ok.step.start(x)
    case NInt{}:
      number.ok.step.int(x)
    case NZero{}:
      number.ok.step.body(x, False{})
    case NDig{}:
      number.ok.step.body(x, True{})
    case NDot{}:
      number.ok.step.frac(x, False{})
    case NFrac{}:
      number.ok.step.frac(x, True{})
    case NExp{}:
      number.ok.step.exps(x)
    case NExpN{}:
      number.ok.step.expd(x)
    case NExpD{}:
      number.ok.step.expd(x)
    case NBad{}:
      NBad{}

def number.ok.done(st: Num) -> Bool:
  match st:
    case NZero{}:
      True{}
    case NDig{}:
      True{}
    case NFrac{}:
      True{}
    case NExpD{}:
      True{}
    case other:
      False{}

def number.ok.go(cs: List<&2, Char>, st: Num) -> Bool:
  match cs:
    case Nil{}:
      number.ok.done(st)
    case Con{c, t}:
      number.ok.go(t, number.ok.step(st, Char.to_u32(c)))

# whether text is a JSON number
def number.ok(s: String) -> Bool:
  number.ok.go(String.to_list(s), NStart{})

# a JSON number written as text, or null when the text is not one
def number(+raw: String) -> Json:
  number.go(raw, number.ok(raw))

# a finite float, in Bend's spelling; infinity and NaN are null
def f32(x: F32) -> Json:
  number(F32.show(x))

# the value of a key in a chain of pairs; JNull when the key is absent
def find(cells: Json, +key: String) -> Json:
  match cells:
    case JPair{+k, v, r}:
      Lazy.stop(Json, String.eq(k, key), v, _u => find(r, key))
    case other:
      JNull{}

# an object's value at a key; JNull when it is not an object or has no such
# key. A repeated key reads as the first value.
def get(j: Json, key: String) -> Json:
  match j:
    case JObj{pairs}:
      find(pairs, key)
    case other:
      JNull{}

def at.go(cells: Json, +i: U32) -> Json:
  match cells:
    case JCons{h, t}:
      Lazy.stop(Json, U32.is_zero(i), h, _u => at.go(t, U32.sub(i, 1)))
    case other:
      JNull{}

# an array's item at an index; JNull when it is not an array or has none
def at(j: Json, i: U32) -> Json:
  match j:
    case JArr{items}:
      at.go(items, i)
    case other:
      JNull{}

# a string's text, else the default
def str_or(j: Json, default: String) -> String:
  match j:
    case JStr{s}:
      s
    case other:
      default

# a boolean, else the default
def bool_or(j: Json, default: Bool) -> Bool:
  match j:
    case JBool{b}:
      b
    case other:
      default

# a number as a U32, else the default
def u32_or(j: Json, default: U32) -> U32:
  match j:
    case JNum{raw}:
      Maybe.default(&2, U32, U32.read(raw), default)
    case other:
      default

# a number as an F32, else the default
def f32_or(j: Json, default: F32) -> F32:
  match j:
    case JNum{raw}:
      Maybe.default(&2, F32, F32.read(raw), default)
    case other:
      default

# an array's first item
def first(j: Json) -> Json:
  match j:
    case JArr{JCons{h, t}}:
      h
    case other:
      JNull{}
