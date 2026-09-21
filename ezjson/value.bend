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

def num.go(raw: String, ok: Bool) -> Json:
  match ok:
    case True{}:
      JNum{raw}
    case False{}:
      JNull{}

def num.ok.digit(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def num.ok.expmark(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 101), U32.is_eq(x, 69))

def num.ok.lead(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 49), U32.is_le(x, 57))

def num.ok.step.lead(ok: Bool) -> Num:
  match ok:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def num.ok.step.int.go(+x: U32, zero: Bool) -> Num:
  match zero:
    case True{}:
      NZero{}
    case False{}:
      num.ok.step.lead(num.ok.lead(x))

def num.ok.step.int(+x: U32) -> Num:
  num.ok.step.int.go(x, U32.is_eq(x, 48))

def num.ok.step.start.go(+x: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NInt{}
    case False{}:
      num.ok.step.int(x)

def num.ok.step.start(+x: U32) -> Num:
  num.ok.step.start.go(x, U32.is_eq(x, 45))

def num.ok.step.mark.go(mark: Bool) -> Num:
  match mark:
    case True{}:
      NExp{}
    case False{}:
      NBad{}

def num.ok.step.mark(+x: U32) -> Num:
  num.ok.step.mark.go(num.ok.expmark(x))

def num.ok.step.body.digit(more: Bool) -> Num:
  match more:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def num.ok.step.body.other.go(+x: U32, dot: Bool) -> Num:
  match dot:
    case True{}:
      NDot{}
    case False{}:
      num.ok.step.mark(x)

def num.ok.step.body.other(+x: U32) -> Num:
  num.ok.step.body.other.go(x, U32.is_eq(x, 46))

def num.ok.step.body.go(+x: U32, more: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      num.ok.step.body.digit(more)
    case False{}:
      num.ok.step.body.other(x)

def num.ok.step.body(+x: U32, more: Bool) -> Num:
  num.ok.step.body.go(x, more, num.ok.digit(x))

def num.ok.step.frac.other(+x: U32, have: Bool) -> Num:
  match have:
    case True{}:
      num.ok.step.mark(x)
    case False{}:
      NBad{}

def num.ok.step.frac.go(+x: U32, have: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      NFrac{}
    case False{}:
      num.ok.step.frac.other(x, have)

def num.ok.step.frac(+x: U32, have: Bool) -> Num:
  num.ok.step.frac.go(x, have, num.ok.digit(x))

def num.ok.step.expd.go(digit: Bool) -> Num:
  match digit:
    case True{}:
      NExpD{}
    case False{}:
      NBad{}

def num.ok.step.expd(+x: U32) -> Num:
  num.ok.step.expd.go(num.ok.digit(x))

def num.ok.step.exps.minus.go(+x: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NExpN{}
    case False{}:
      num.ok.step.expd(x)

def num.ok.step.exps.minus(+x: U32) -> Num:
  num.ok.step.exps.minus.go(x, U32.is_eq(x, 45))

def num.ok.step.exps.go(+x: U32, plus: Bool) -> Num:
  match plus:
    case True{}:
      NExpN{}
    case False{}:
      num.ok.step.exps.minus(x)

def num.ok.step.exps(+x: U32) -> Num:
  num.ok.step.exps.go(x, U32.is_eq(x, 43))

def num.ok.step(st: Num, +x: U32) -> Num:
  match st:
    case NStart{}:
      num.ok.step.start(x)
    case NInt{}:
      num.ok.step.int(x)
    case NZero{}:
      num.ok.step.body(x, False{})
    case NDig{}:
      num.ok.step.body(x, True{})
    case NDot{}:
      num.ok.step.frac(x, False{})
    case NFrac{}:
      num.ok.step.frac(x, True{})
    case NExp{}:
      num.ok.step.exps(x)
    case NExpN{}:
      num.ok.step.expd(x)
    case NExpD{}:
      num.ok.step.expd(x)
    case NBad{}:
      NBad{}

def num.ok.done(st: Num) -> Bool:
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

def num.ok.go(cs: List<&2, Char>, st: Num) -> Bool:
  match cs:
    case Nil{}:
      num.ok.done(st)
    case Con{c, t}:
      num.ok.go(t, num.ok.step(st, Char.to_u32(c)))

# whether text is a JSON number
def num.ok(s: String) -> Bool:
  num.ok.go(String.to_list(s), NStart{})

# a JSON number from its text, or null when that text is not one
def num(+raw: String) -> Json:
  num.go(raw, num.ok(raw))

# character-for-character equality. `String.eq` rebuilds both strings and
# discards the copies; a search only needs the bool. A mismatch stops.
def find.eq.go(left: String, right: String, same: Bool) -> Bool:
  match left right same:
    case SNil{} SNil{} True{}:
      True{}
    case SCon{+x, xs} SCon{+y, ys} True{}:
      find.eq.go(xs, ys, Char.is_eq(x, y))
    case l r s:
      False{}

def find.eq(a: String, b: String) -> Bool:
  find.eq.go(a, b, True{})

# the matched value, or the next pair when the key differs
def find.at(rest: Json, +key: String, eq: Bool, v: Json) -> Json:
  match rest key eq v:
    case r k True{} val:
      val
    case JPair{k2, v2, r2} k False{} val:
      find.at(r2, k, find.eq(k2, k), v2)
    case r k s val:
      JNull{}

# the value of a key in a chain of pairs; JNull when the key is absent
def find(cells: Json, +key: String) -> Json:
  match cells:
    case JPair{k, v, r}:
      find.at(r, key, find.eq(k, key), v)
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

# a string, or none when the value is not one
def as_str(j: Json) -> Maybe<&2, String>:
  match j:
    case JStr{s}:
      Some{s}
    case other:
      None{}

# a boolean, or none when the value is not one
def as_bool(j: Json) -> Maybe<&2, Bool>:
  match j:
    case JBool{b}:
      Some{b}
    case other:
      None{}

# a number's text, or none when the value is not a number
def as_num(j: Json) -> Maybe<&2, String>:
  match j:
    case JNum{raw}:
      Some{raw}
    case other:
      None{}

# a number as a U32, or none when it is not one or does not fit
def as_u32(j: Json) -> Maybe<&2, U32>:
  match j:
    case JNum{raw}:
      U32.read(raw)
    case other:
      None{}

# a number as an F32, or none when it is not one or does not fit
def as_f32(j: Json) -> Maybe<&2, F32>:
  match j:
    case JNum{raw}:
      F32.read(raw)
    case other:
      None{}
