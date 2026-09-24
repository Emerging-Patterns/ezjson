# src/value: a JSON value. Null, bool, number, string, array, and object.
# An array is a JArr of JCons cells ending in JNil; an object is a JObj of
# JPair cells ending in JNil. A number keeps its source text.
import Base
import ./lazy.bend as Lazy

# a JSON value; JNil, JCons and JPair are the cells of arrays and objects.
# JSpan and JBind are the same string and key, as the first `n` chars of a
# source suffix, so a parse does not copy that text.
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
  JSpan{src: String, n: U32}
  JBind{src: String, n: U32, val: Json, rest: Json}

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

# the first `nn` chars of `src` as their own string
def span.str(src: String, +nn: U32, zero: Bool) -> String:
  match src zero:
    case s True{}:
      ""
    case SNil{} False{}:
      ""
    case SCon{h, t} False{}:
      SCon{h, span.str(t, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))}

# whether the first `nn` chars of `src` equal `key`, stopping at the first miss.
# A count past the end of `src` covers what there is, as span.str reads it
def span.eq.go(src: String, same: Bool, zero: Bool, key: String, +nn: U32) -> Bool:
  match src same zero key:
    case s False{} zero k:
      False{}
    case s True{} True{} SNil{}:
      True{}
    case s True{} True{} k:
      False{}
    case SCon{+a, as} True{} False{} SCon{+b, bs}:
      span.eq.go(as, Char.is_eq(a, b), U32.is_zero(U32.sub(nn, 1)), bs, U32.sub(nn, 1))
    case SNil{} True{} False{} SNil{}:
      True{}
    case s True{} False{} k:
      False{}

# whether the first `nn` chars of `src` are `key`
def span.eq(+src: String, +nn: U32, +key: String) -> Bool:
  span.eq.go(src, True{}, U32.is_zero(nn), key, nn)

# reverses a chain of JCons or JPair cells onto acc
def reverse(cells: Json, acc: Json) -> Json:
  match cells:
    case JCons{h, t}:
      reverse(t, JCons{h, acc})
    case JPair{k, v, r}:
      reverse(r, JPair{k, v, acc})
    case JBind{src, n, v, r}:
      reverse(r, JBind{src, n, v, acc})
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
def bool(flag: Bool) -> Json:
  JBool{flag}

# a string
def str(txt: String) -> Json:
  JStr{txt}

def num.go(raw: String, ok: Bool) -> Json:
  match ok:
    case True{}:
      JNum{raw}
    case False{}:
      JNull{}

def num.ok.digit(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57))

def num.ok.expmark(+cp: U32) -> Bool:
  Bool.or(U32.is_eq(cp, 101), U32.is_eq(cp, 69))

def num.ok.lead(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 49), U32.is_le(cp, 57))

def num.ok.step.lead(ok: Bool) -> Num:
  match ok:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def num.ok.step.int.go(+cp: U32, zero: Bool) -> Num:
  match zero:
    case True{}:
      NZero{}
    case False{}:
      num.ok.step.lead(num.ok.lead(cp))

def num.ok.step.int(+cp: U32) -> Num:
  num.ok.step.int.go(cp, U32.is_eq(cp, 48))

def num.ok.step.start.go(+cp: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NInt{}
    case False{}:
      num.ok.step.int(cp)

def num.ok.step.start(+cp: U32) -> Num:
  num.ok.step.start.go(cp, U32.is_eq(cp, 45))

def num.ok.step.mark.go(mark: Bool) -> Num:
  match mark:
    case True{}:
      NExp{}
    case False{}:
      NBad{}

def num.ok.step.mark(+cp: U32) -> Num:
  num.ok.step.mark.go(num.ok.expmark(cp))

def num.ok.step.body.digit(more: Bool) -> Num:
  match more:
    case True{}:
      NDig{}
    case False{}:
      NBad{}

def num.ok.step.body.other.go(+cp: U32, dot: Bool) -> Num:
  match dot:
    case True{}:
      NDot{}
    case False{}:
      num.ok.step.mark(cp)

def num.ok.step.body.other(+cp: U32) -> Num:
  num.ok.step.body.other.go(cp, U32.is_eq(cp, 46))

def num.ok.step.body.go(+cp: U32, more: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      num.ok.step.body.digit(more)
    case False{}:
      num.ok.step.body.other(cp)

def num.ok.step.body(+cp: U32, more: Bool) -> Num:
  num.ok.step.body.go(cp, more, num.ok.digit(cp))

def num.ok.step.frac.other(+cp: U32, have: Bool) -> Num:
  match have:
    case True{}:
      num.ok.step.mark(cp)
    case False{}:
      NBad{}

def num.ok.step.frac.go(+cp: U32, have: Bool, digit: Bool) -> Num:
  match digit:
    case True{}:
      NFrac{}
    case False{}:
      num.ok.step.frac.other(cp, have)

def num.ok.step.frac(+cp: U32, have: Bool) -> Num:
  num.ok.step.frac.go(cp, have, num.ok.digit(cp))

def num.ok.step.expd.go(digit: Bool) -> Num:
  match digit:
    case True{}:
      NExpD{}
    case False{}:
      NBad{}

def num.ok.step.expd(+cp: U32) -> Num:
  num.ok.step.expd.go(num.ok.digit(cp))

def num.ok.step.exps.minus.go(+cp: U32, minus: Bool) -> Num:
  match minus:
    case True{}:
      NExpN{}
    case False{}:
      num.ok.step.expd(cp)

def num.ok.step.exps.minus(+cp: U32) -> Num:
  num.ok.step.exps.minus.go(cp, U32.is_eq(cp, 45))

def num.ok.step.exps.go(+cp: U32, plus: Bool) -> Num:
  match plus:
    case True{}:
      NExpN{}
    case False{}:
      num.ok.step.exps.minus(cp)

def num.ok.step.exps(+cp: U32) -> Num:
  num.ok.step.exps.go(cp, U32.is_eq(cp, 43))

def num.ok.step(st: Num, +cp: U32) -> Num:
  match st:
    case NStart{}:
      num.ok.step.start(cp)
    case NInt{}:
      num.ok.step.int(cp)
    case NZero{}:
      num.ok.step.body(cp, False{})
    case NDig{}:
      num.ok.step.body(cp, True{})
    case NDot{}:
      num.ok.step.frac(cp, False{})
    case NFrac{}:
      num.ok.step.frac(cp, True{})
    case NExp{}:
      num.ok.step.exps(cp)
    case NExpN{}:
      num.ok.step.expd(cp)
    case NExpD{}:
      num.ok.step.expd(cp)
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
def num.ok(txt: String) -> Bool:
  num.ok.go(String.to_list(txt), NStart{})

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

def find.eq(lhs: String, rhs: String) -> Bool:
  find.eq.go(lhs, rhs, True{})

# the matched value, or the next pair when the key differs
def find.at(rest: Json, +key: String, eq: Bool, vv: Json) -> Json:
  match rest key eq vv:
    case r k True{} val:
      val
    case JPair{k2, v2, r2} k False{} val:
      find.at(r2, k, find.eq(k2, k), v2)
    case JBind{src, n, v2, r2} k False{} val:
      find.at(r2, k, span.eq(src, n, k), v2)
    case r k s val:
      JNull{}

# the value of a key in a chain of pairs; JNull when the key is absent
def find(cells: Json, +key: String) -> Json:
  match cells:
    case JPair{k, v, r}:
      find.at(r, key, find.eq(k, key), v)
    case JBind{src, n, v, r}:
      find.at(r, key, span.eq(src, n, key), v)
    case other:
      JNull{}

# an object's value at a key; JNull when it is not an object or has no such
# key. A repeated key reads as the first value.
def get(val: Json, key: String) -> Json:
  match val:
    case JObj{pairs}:
      find(pairs, key)
    case other:
      JNull{}

def at.go(cells: Json, +idx: U32) -> Json:
  match cells:
    case JCons{h, t}:
      Lazy.stop(Json, U32.is_zero(idx), h, _u => at.go(t, U32.sub(idx, 1)))
    case other:
      JNull{}

# an array's item at an index; JNull when it is not an array or has none
def at(val: Json, idx: U32) -> Json:
  match val:
    case JArr{items}:
      at.go(items, idx)
    case other:
      JNull{}

# what wf.go checks: a value, the cells of an array, or the cells of an object
type Shape is Data:
  WVal{}
  WArr{}
  WObj{}

# whether a value, or a chain of cells, has the shape the parser and the
# builders give: arrays and objects are chains of cells ending in JNil, no
# cell stands where a value belongs, and a number's text is a JSON number
def wf.go(val: Json, shape: Shape) -> Bool:
  match val shape:
    case JNull{} WVal{}:
      True{}
    case JBool{_} WVal{}:
      True{}
    case JNum{raw} WVal{}:
      num.ok(raw)
    case JStr{_} WVal{}:
      True{}
    case JSpan{_, _} WVal{}:
      True{}
    case JArr{items} WVal{}:
      wf.go(items, WArr{})
    case JObj{pairs} WVal{}:
      wf.go(pairs, WObj{})
    case JNil{} WArr{}:
      True{}
    case JCons{hd, tl} WArr{}:
      Lazy.stop(Bool, Bool.not(wf.go(hd, WVal{})), False{}, _u => wf.go(tl, WArr{}))
    case JNil{} WObj{}:
      True{}
    case JPair{_, vv, rr} WObj{}:
      Lazy.stop(Bool, Bool.not(wf.go(vv, WVal{})), False{}, _u => wf.go(rr, WObj{}))
    case JBind{_, _, vv, rr} WObj{}:
      Lazy.stop(Bool, Bool.not(wf.go(vv, WVal{})), False{}, _u => wf.go(rr, WObj{}))
    case _ _:
      False{}

# whether a value is well-formed: the shape every value from the builders and
# from parse has. print writes JSON text for exactly these
def wf(val: Json) -> Bool:
  wf.go(val, WVal{})

# whether a chain of pairs has the key, stopping at the first match
def has.go(cells: Json, +key: String) -> Bool:
  match cells:
    case JPair{k2, _, rr}:
      Lazy.stop(Bool, find.eq(k2, key), True{}, _u => has.go(rr, key))
    case JBind{src, nn, _, rr}:
      Lazy.stop(Bool, span.eq(src, nn, key), True{}, _u => has.go(rr, key))
    case _:
      False{}

# whether an object has the key; false when the value is not an object
def has(val: Json, key: String) -> Bool:
  match val:
    case JObj{pairs}:
      has.go(pairs, key)
    case _:
      False{}

# how many cells a chain of array or object cells holds
def len.go(cells: Json) -> Nat:
  match cells:
    case JCons{_, tl}:
      1n+len.go(tl)
    case JPair{_, _, rr}:
      1n+len.go(rr)
    case JBind{_, _, _, rr}:
      1n+len.go(rr)
    case _:
      0n

# how many elements an array, or members an object, has; 0 for anything else
def len(val: Json) -> U32:
  match val:
    case JArr{items}:
      U32.from_nat(len.go(items))
    case JObj{pairs}:
      U32.from_nat(len.go(pairs))
    case _:
      0

# a string, or none when the value is not one
def as_str(val: Json) -> Maybe<&2, String>:
  match val:
    case JStr{s}:
      Some{s}
    case JSpan{src, +n}:
      Some{span.str(src, n, U32.is_zero(n))}
    case other:
      None{}

# a boolean, or none when the value is not one
def as_bool(val: Json) -> Maybe<&2, Bool>:
  match val:
    case JBool{b}:
      Some{b}
    case other:
      None{}

# a number's text, or none when the value is not a number
def as_num(val: Json) -> Maybe<&2, String>:
  match val:
    case JNum{raw}:
      Some{raw}
    case other:
      None{}

# a number as a U32, or none when it is not one or does not fit
def as_u32(val: Json) -> Maybe<&2, U32>:
  match val:
    case JNum{raw}:
      U32.read(raw)
    case other:
      None{}

# the largest finite F32
def f32.top() -> F32:
  3.4028235e38

# a read that stayed finite; none when it did not. A JSON number never spells
# infinity, so an infinite read is a number too large for F32
def f32.fit.go(xx: F32, finite: Bool) -> Maybe<&2, F32>:
  match finite:
    case True{}:
      Some{xx}
    case False{}:
      None{}

# a read that stayed finite, or none
def f32.fit(got: Maybe<&2, F32>) -> Maybe<&2, F32>:
  match got:
    case Some{+xx}:
      f32.fit.go(xx, F32.is_le(F32.abs(xx), f32.top()))
    case None{}:
      None{}

# a number as an F32, or none when it is not one or does not fit
def as_f32(val: Json) -> Maybe<&2, F32>:
  match val:
    case JNum{raw}:
      f32.fit(F32.read(raw))
    case other:
      None{}
