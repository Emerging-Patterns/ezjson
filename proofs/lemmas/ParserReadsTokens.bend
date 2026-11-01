# the parser on a value's tokens: slots, pushes and closing brackets
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2
import ./NumberCharsAreWordChars.bend as M3
import ./WellFormedCells.bend as M4

# a word equal to a literal is no number
law lit_not_num:
  for +raw: String
  for +lit: String
  for e_lit: {String.eq(raw, lit) == True{} : Bool}
  for h_lit: {V.num.ok(lit) == False{} : Bool}
  for h_num: {V.num.ok(raw) == True{} : Bool}
  Empty

def lit_not_num(raw, lit, e_lit, h_lit, h_num):
  M1.true_false(Equal.trans(Bool, True{}, V.num.ok(raw), False{}, Equal.sym(Bool, V.num.ok(raw), True{}, h_num),
    Equal.trans(Bool, V.num.ok(raw), V.num.ok(lit), False{},
      Equal.cong(String, Bool, zz => V.num.ok(zz), raw, lit, M3.str_eq_sound(raw, lit, e_lit)), h_lit)))

# a number's word, with the literal tests named: the parser takes it as that number
law word_num.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for e1: {String.eq(raw, "null") == b1 : Bool}
  for e2: {String.eq(raw, "true") == b2 : Bool}
  for e3: {String.eq(raw, "false") == b3 : Bool}
  for +h_num: {V.num.ok(raw) == True{} : Bool}
  ({Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3, V.JBool{False{}},
    V.JNum{raw}))) == V.JNum{raw} : V.Json} & {Bool.or(b1, Bool.or(b2, Bool.or(b3, V.num.ok(raw)))) == True{} : Bool})

def word_num.at(b1, b2, b3, raw, e1, e2, e3, h_num):
  match b1:
    case True{}:
      Empty.absurd(({V.JNull{} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
        lit_not_num(raw, "null", e1, {==}, h_num))
    case False{}:
      match b2:
        case True{}:
          Empty.absurd(({V.JBool{True{}} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
            lit_not_num(raw, "true", e2, {==}, h_num))
        case False{}:
          match b3:
            case True{}:
              Empty.absurd(({V.JBool{False{}} == V.JNum{raw} : V.Json} & {True{} == True{} : Bool}),
                lit_not_num(raw, "false", e3, {==}, h_num))
            case False{}:
              ({==}, h_num)

# step_num, with the word's two facts in hand
law step_num.go:
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for both: ({Parse.word(raw) == V.JNum{raw} : V.Json} & {Parse.word.ok(raw) == True{} : Bool})
  {Parse.step.word(raw, Parse.P{bad, root, stk}) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}

def step_num.go(raw, bad, root, stk, both):
  (ew, eo) = both
  ok = Equal.sym(Bool, Parse.word.ok(raw), True{}, eo)
  %ok : {Parse.step.word.go(raw, Parse.P{bad, root, stk}, _) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}
  ws = Equal.sym(V.Json, Parse.word(raw), V.JNum{raw}, ew)
  %ws : {Parse.put(stk, root, _, bad) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}
  {==}

# the parser on a number's word, at a place a value may go
law step_num:
  for +raw: String
  for h_num: {V.num.ok(raw) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.step.word(raw, Parse.P{bad, root, stk}) == Parse.put(stk, root, V.JNum{raw}, bad) : Parse.P}

def step_num(raw, h_num, bad, root, stk):
  both = word_num.at(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw, {==}, {==}, {==},
    h_num)
  step_num.go(raw, bad, root, stk, both)

# a value as parse builds it back from its tokens: strings owned and fixed,
# span keys owned, by shape as tj reads it
def canon_r(val: V.Json, sh: V.Shape) -> V.Json:
  match val sh:
    case V.JNull{} V.WVal{}:
      V.JNull{}
    case V.JBool{bb} V.WVal{}:
      V.JBool{bb}
    case V.JNum{raw} V.WVal{}:
      V.JNum{raw}
    case V.JStr{txt} V.WVal{}:
      V.JStr{txt}
    case V.JSpan{src, +nn} V.WVal{}:
      V.JStr{V.span.str(src, nn, U32.is_zero(nn))}
    case V.JArr{items} V.WVal{}:
      V.JArr{canon_r(items, V.WArr{})}
    case V.JObj{pairs} V.WVal{}:
      V.JObj{canon_r(pairs, V.WObj{})}
    case V.JCons{hd, tl} V.WArr{}:
      V.JCons{canon_r(hd, V.WVal{}), canon_r(tl, V.WArr{})}
    case V.JPair{kk, vv, rr} V.WObj{}:
      V.JPair{kk, canon_r(vv, V.WVal{}), canon_r(rr, V.WObj{})}
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), canon_r(rr, V.WObj{})}
    case _ _:
      V.JNil{}

# an array's cells pushed, as parse pushes them, onto its frame's items
def rpush_r(cells: V.Json, acc: V.Json) -> V.Json:
  match cells:
    case V.JCons{hd, tl}:
      rpush_r(tl, V.JCons{canon_r(hd, V.WVal{}), acc})
    case _:
      acc

# an object's cells pushed, as parse pushes them, onto its frame's pairs
def ppush_r(cells: V.Json, acc: V.Json) -> V.Json:
  match cells:
    case V.JPair{kk, vv, rr}:
      ppush_r(rr, V.JPair{kk, canon_r(vv, V.WVal{}), acc})
    case V.JBind{src, +nn, vv, rr}:
      ppush_r(rr, V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc})
    case _:
      acc

# an array frame's slot after its cells: a value still, when there were none
def aslot(cells: V.Json) -> Parse.Slot:
  match cells:
    case V.JNil{}:
      Parse.SValue{}
    case _:
      Parse.SComma{}

# an object frame's slot after its cells: a key still, when there were none
def oslot(cells: V.Json) -> Parse.Slot:
  match cells:
    case V.JNil{}:
      Parse.SKey{}
    case _:
      Parse.SComma{}

# the parser on two token lists is the parser on the first, then the second
law prun_app:
  for +xs: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  for +st: Parse.P
  {Parse.run(List.append(&2, Lex.Tok, xs, ys), st) == Parse.run(ys, Parse.run(xs, st)) : Parse.P}

def prun_app(xs, ys, st):
  match xs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      prun_app(tl, ys, Parse.step(hd, st))

# what put_str_ready says
def psr_goal(+stk: List<&2, Parse.Frame>, +root: Maybe<&2, V.Json>, +txt: String, +bad: Bool) -> Type:
  {Parse.put.str(stk, root, Parse.KOwn{txt}, bad) == Parse.put(stk, root, V.JStr{txt}, bad) : Parse.P}

# a string where a value may go is that value
law put_str_ready:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +txt: String
  for +bad: Bool
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  psr_goal(stk, root, txt, bad)

def put_str_ready(stk, root, txt, bad, h):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          {==}
        case Some{+rr}:
          Empty.absurd(psr_goal([], Some{rr}, txt, bad), M2.false_true(h))
    case +fr <> +rest:
      match fr:
        case Parse.FArr{+items, +slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SComma{}} <> rest, root, txt, bad), M2.false_true(h))
            case Parse.SKey{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SKey{}} <> rest, root, txt, bad), M2.false_true(h))
            case Parse.SColon{}:
              Empty.absurd(psr_goal(Parse.FArr{items, Parse.SColon{}} <> rest, root, txt, bad), M2.false_true(h))
        case Parse.FObj{+pairs, +key, +slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SComma{}} <> rest, root, txt, bad), M2.false_true(h))
            case Parse.SKey{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SKey{}} <> rest, root, txt, bad), M2.false_true(h))
            case Parse.SColon{}:
              Empty.absurd(psr_goal(Parse.FObj{pairs, key, Parse.SColon{}} <> rest, root, txt, bad), M2.false_true(h))

# `[` where a value may go opens an array
law open_arr_ready:
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  {Parse.step.open_arr(Parse.P{bad, root, stk}) == Parse.P{bad, root, Parse.FArr{V.JNil{},
    Parse.SValue{}} <> stk} : Parse.P}

def open_arr_ready(bad, root, stk, h):
  hs = Equal.sym(Bool, Parse.step.ready(stk, root), True{}, h)
  %hs : {Parse.step.open_arr.go(bad, root, stk, _) == Parse.P{bad, root, Parse.FArr{V.JNil{},
    Parse.SValue{}} <> stk} : Parse.P}
  {==}

# `{` where a value may go opens an object
law open_obj_ready:
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: {Parse.step.ready(stk, root) == True{} : Bool}
  {Parse.step.open_obj(Parse.P{bad, root, stk}) == Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
    Parse.SKey{}} <> stk} : Parse.P}

def open_obj_ready(bad, root, stk, h):
  hs = Equal.sym(Bool, Parse.step.ready(stk, root), True{}, h)
  %hs : {Parse.step.open_obj.go(bad, root, stk, _) == Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
    Parse.SKey{}} <> stk} : Parse.P}
  {==}

# pushing an array's cells then reversing them gives the cells back in order
law rev_rpush_r:
  for +cells: V.Json
  for +acc: V.Json
  {V.reverse(rpush_r(cells, acc), V.JNil{}) == V.reverse(acc, canon_r(cells, V.WArr{})) : V.Json}

def rev_rpush_r(cells, acc):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      rev_rpush_r(x2, V.JCons{canon_r(x1, V.WVal{}), acc})
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# pushing an object's cells then reversing them gives the cells back in order
law rev_ppush_r:
  for +cells: V.Json
  for +acc: V.Json
  {V.reverse(ppush_r(cells, acc), V.JNil{}) == V.reverse(acc, canon_r(cells, V.WObj{})) : V.Json}

def rev_ppush_r(cells, acc):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      rev_ppush_r(x3, V.JPair{x1, canon_r(x2, V.WVal{}), acc})
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      rev_ppush_r(x4, V.JPair{V.span.str(x1, x2, U32.is_zero(x2)), canon_r(x3, V.WVal{}), acc})

# `]` after an array's cells
law close_after_arr_r:
  for +items: V.Json
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.close_arr(Parse.FArr{rpush_r(items, V.JNil{}), aslot(items)} <> stk, root, bad) ==
    Parse.put(stk, root, V.JArr{canon_r(items, V.WArr{})}, bad) : Parse.P}

def close_after_arr_r(items, bad, root, stk):
  match items:

    case V.JNull{}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JNull{}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JNull{}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JNull{}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JNull{}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JNull{}, V.JNil{}),
          V.JNil{}), canon_r(V.JNull{}, V.WArr{}), rev_rpush_r(V.JNull{}, V.JNil{})))
    case V.JBool{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JBool{x1}, V.JNil{}), Parse.SComma{}} <> stk, root,
        bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JBool{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JBool{x1}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JBool{x1}, V.JNil{}), stk, root,
            bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JBool{x1},
          V.JNil{}), V.JNil{}), canon_r(V.JBool{x1}, V.WArr{}), rev_rpush_r(V.JBool{x1}, V.JNil{})))
    case V.JNum{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JNum{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JNum{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JNum{x1}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JNum{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JNum{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JNum{x1}, V.WArr{}), rev_rpush_r(V.JNum{x1}, V.JNil{})))
    case V.JStr{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JStr{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JStr{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JStr{x1}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JStr{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JStr{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JStr{x1}, V.WArr{}), rev_rpush_r(V.JStr{x1}, V.JNil{})))
    case V.JArr{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JArr{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JArr{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JArr{x1}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JArr{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JArr{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JArr{x1}, V.WArr{}), rev_rpush_r(V.JArr{x1}, V.JNil{})))
    case V.JObj{+x1}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JObj{x1}, V.JNil{}), Parse.SComma{}} <> stk, root, bad),
        Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JObj{x1}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root,
        V.JArr{canon_r(V.JObj{x1}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JObj{x1}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JObj{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JObj{x1}, V.WArr{}), rev_rpush_r(V.JObj{x1}, V.JNil{})))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JCons{x1, x2}, V.JNil{}), Parse.SComma{}} <> stk, root,
        bad), Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JCons{x1, x2}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk,
        root, V.JArr{canon_r(V.JCons{x1, x2}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JCons{x1, x2}, V.JNil{}),
            stk,
        root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JCons{x1, x2},
          V.JNil{}), V.JNil{}), canon_r(V.JCons{x1, x2}, V.WArr{}), rev_rpush_r(V.JCons{x1, x2}, V.JNil{})))
    case V.JPair{+x1, +x2, +x3}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JPair{x1, x2, x3}, V.JNil{}), Parse.SComma{}} <> stk,
        root, bad), Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JPair{x1, x2, x3}, V.JNil{}), V.JNil{})}, bad),
        Parse.put(stk, root, V.JArr{canon_r(V.JPair{x1, x2, x3}, V.WArr{})}, bad),
            M2.close_arr_comma(rpush_r(V.JPair{x1,
          x2,
        x3}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JPair{x1, x2, x3},
          V.JNil{}), V.JNil{}), canon_r(V.JPair{x1, x2, x3}, V.WArr{}), rev_rpush_r(V.JPair{x1, x2, x3}, V.JNil{})))
    case V.JSpan{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JSpan{x1, x2}, V.JNil{}), Parse.SComma{}} <> stk, root,
        bad), Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JSpan{x1, x2}, V.JNil{}), V.JNil{})}, bad), Parse.put(stk,
        root, V.JArr{canon_r(V.JSpan{x1, x2}, V.WArr{})}, bad), M2.close_arr_comma(rpush_r(V.JSpan{x1, x2}, V.JNil{}),
            stk,
        root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JSpan{x1, x2},
          V.JNil{}), V.JNil{}), canon_r(V.JSpan{x1, x2}, V.WArr{}), rev_rpush_r(V.JSpan{x1, x2}, V.JNil{})))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(Parse.P, Parse.close_arr(Parse.FArr{rpush_r(V.JBind{x1, x2, x3, x4}, V.JNil{}),
        Parse.SComma{}} <> stk,
        root, bad), Parse.put(stk, root, V.JArr{V.reverse(rpush_r(V.JBind{x1, x2, x3, x4}, V.JNil{}), V.JNil{})}, bad),
        Parse.put(stk, root, V.JArr{canon_r(V.JBind{x1, x2, x3, x4}, V.WArr{})}, bad),
          M2.close_arr_comma(rpush_r(V.JBind{x1,
        x2, x3, x4}, V.JNil{}), stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JArr{zz}, bad), V.reverse(rpush_r(V.JBind{x1, x2, x3,
          x4}, V.JNil{}), V.JNil{}), canon_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), rev_rpush_r(V.JBind{x1, x2, x3, x4},
          V.JNil{})))

# `}` after an object's cells
law close_after_obj_r:
  for +pairs: V.Json
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.close_obj(Parse.FObj{ppush_r(pairs, V.JNil{}), Parse.KOwn{""}, oslot(pairs)} <> stk, root, bad) ==
    Parse.put(stk, root, V.JObj{canon_r(pairs, V.WObj{})}, bad) : Parse.P}

def close_after_obj_r(pairs, bad, root, stk):
  match pairs:
    case V.JNull{}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JNull{}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JNull{}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JNull{}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JNull{}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JNull{}, V.JNil{}),
          V.JNil{}), canon_r(V.JNull{}, V.WObj{}), rev_ppush_r(V.JNull{}, V.JNil{})))
    case V.JBool{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JBool{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JBool{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JBool{x1}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JBool{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JBool{x1},
          V.JNil{}), V.JNil{}), canon_r(V.JBool{x1}, V.WObj{}), rev_ppush_r(V.JBool{x1}, V.JNil{})))
    case V.JNum{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JNum{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JNum{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JNum{x1}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JNum{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JNum{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JNum{x1}, V.WObj{}), rev_ppush_r(V.JNum{x1}, V.JNil{})))
    case V.JStr{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JStr{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JStr{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JStr{x1}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JStr{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JStr{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JStr{x1}, V.WObj{}), rev_ppush_r(V.JStr{x1}, V.JNil{})))
    case V.JArr{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JArr{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JArr{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JArr{x1}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JArr{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JArr{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JArr{x1}, V.WObj{}), rev_ppush_r(V.JArr{x1}, V.JNil{})))
    case V.JObj{+x1}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JObj{x1}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JObj{x1}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JObj{x1}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JObj{x1}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JObj{x1},
          V.JNil{}),
          V.JNil{}), canon_r(V.JObj{x1}, V.WObj{}), rev_ppush_r(V.JObj{x1}, V.JNil{})))
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JCons{x1, x2}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JCons{x1, x2}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JCons{x1, x2}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JCons{x1, x2}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JCons{x1, x2},
          V.JNil{}), V.JNil{}), canon_r(V.JCons{x1, x2}, V.WObj{}), rev_ppush_r(V.JCons{x1, x2}, V.JNil{})))
    case V.JPair{+x1, +x2, +x3}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JPair{x1, x2, x3}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JPair{x1, x2, x3},
          V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JPair{x1, x2, x3}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JPair{x1, x2, x3}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JPair{x1, x2, x3},
          V.JNil{}), V.JNil{}), canon_r(V.JPair{x1, x2, x3}, V.WObj{}), rev_ppush_r(V.JPair{x1, x2, x3}, V.JNil{})))
    case V.JSpan{+x1, +x2}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JSpan{x1, x2}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JSpan{x1, x2}, V.JNil{}),
        V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JSpan{x1, x2}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JSpan{x1, x2}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JSpan{x1, x2},
          V.JNil{}), V.JNil{}), canon_r(V.JSpan{x1, x2}, V.WObj{}), rev_ppush_r(V.JSpan{x1, x2}, V.JNil{})))
    case V.JBind{+x1, +x2, +x3, +x4}:
      Equal.trans(Parse.P, Parse.close_obj(Parse.FObj{ppush_r(V.JBind{x1, x2, x3, x4}, V.JNil{}), Parse.KOwn{""},
        Parse.SComma{}} <> stk, root, bad), Parse.put(stk, root, V.JObj{V.reverse(ppush_r(V.JBind{x1, x2, x3, x4},
        V.JNil{}), V.JNil{})}, bad), Parse.put(stk, root, V.JObj{canon_r(V.JBind{x1, x2, x3, x4}, V.WObj{})}, bad),
        M2.close_obj_comma(ppush_r(V.JBind{x1, x2, x3, x4}, V.JNil{}), Parse.KOwn{""}, stk, root, bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, V.JObj{zz}, bad), V.reverse(ppush_r(V.JBind{x1, x2, x3,
          x4}, V.JNil{}), V.JNil{}), canon_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), rev_ppush_r(V.JBind{x1, x2, x3, x4},
          V.JNil{})))

# what pv says of a value by its shape: at a place a value may go, a value's
# tokens put the value; an array's or object's cells push their elements
def pg_r(
  +val: V.Json,
  sh: V.Shape,
  +bad: Bool,
  +root: Maybe<&2, V.Json>,
  +stk: List<&2, Parse.Frame>,
  +acc: V.Json
) -> Type:
  match sh:
    case V.WVal{}:
      {Parse.step.ready(stk, root) == True{} : Bool} ->
        {Parse.run(M4.tj_r(val, V.WVal{}), Parse.P{bad, root, stk}) == Parse.put(stk, root, canon_r(val, V.WVal{}),
          bad) : Parse.P}
    case V.WArr{}:
      {Parse.run(M4.tj_r(val, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}) ==
        Parse.P{bad, root, Parse.FArr{rpush_r(val, acc), aslot(val)} <> stk} : Parse.P}
    case V.WObj{}:
      {Parse.run(M4.tj_r(val, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{""}, Parse.SKey{}} <> stk}) ==
        Parse.P{bad, root, Parse.FObj{ppush_r(val, acc), Parse.KOwn{""}, oslot(val)} <> stk} : Parse.P}

# pv for a boolean
law pv_bool_r:
  for bb: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  pg_r(V.JBool{bb}, V.WVal{}, bad, root, stk, V.JNil{})

def pv_bool_r(bb, _bad, _root, _stk):
  match bb:
    case True{}:
      _hr => {==}
    case False{}:
      _hr => {==}

# pv for an array cell, by what follows it
law pv_cons_r:
  for tl: V.Json
  for +hd: V.Json
  for +h: {V.wf.go(V.JCons{hd, tl}, V.WArr{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_hd: {V.wf.go(hd, V.WVal{}) == True{} : Bool} -> pg_r(hd, V.WVal{}, bad, root, Parse.FArr{acc,
    Parse.SValue{}} <> stk, V.JNil{})
  for ih_tl: {V.wf.go(tl, V.WArr{}) == True{} : Bool} -> pg_r(tl, V.WArr{}, bad, root, stk, V.JCons{canon_r(hd,
    V.WVal{}),
    acc})
  pg_r(V.JCons{hd, tl}, V.WArr{}, bad, root, stk, acc)

def pv_cons_r(tl, hd, h, bad, root, stk, acc, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h)
      ih_hd(hd_ok)({==})
    case V.JNull{}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JNull{}, V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JNull{})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JNull{}, V.JCons{canon_r(hd, V.WVal{}), acc}),
            aslot(V.JNull{})} <> stk},
          Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WArr{}), zz),
            Parse.run(M4.tj_r(hd,
          V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JBool{+x1}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{x1}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBool{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JBool{x1},
          V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JBool{x1})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
            Lex.TComma{} <> M4.tj_r(V.JBool{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JBool{x1}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JNum{+x1}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{x1}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JNum{x1}, V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JNum{x1})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
            Lex.TComma{} <> M4.tj_r(V.JNum{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JNum{x1}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JStr{+x1}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{x1}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JStr{x1}, V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JStr{x1})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
            Lex.TComma{} <> M4.tj_r(V.JStr{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JStr{x1}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JArr{+x1}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{x1}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JArr{x1}, V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JArr{x1})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
            Lex.TComma{} <> M4.tj_r(V.JArr{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JArr{x1}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JObj{+x1}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{x1}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{x1}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{x1},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JObj{x1}, V.JCons{canon_r(hd,
        V.WVal{}), acc}), aslot(V.JObj{x1})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
            Lex.TComma{} <> M4.tj_r(V.JObj{x1},
        V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JObj{x1}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JCons{+x1, +x2}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad,
            root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JCons{x1, x2},
        V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JCons{x1, x2})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WArr{}), Parse.run(M4.tj_r(hd,
            V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1,
              x2},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JCons{x1, x2}, V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JCons{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
              V.WArr{}),
          zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
              Parse.P{bad,
          root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JPair{+x1, +x2, +x3}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2,
        x3},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad,
            root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JPair{x1, x2, x3},
        V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc,
          Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WArr{}), Parse.run(M4.tj_r(hd,
          V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1,
              x2,
          x3}, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JPair{x1, x2, x3}, V.JCons{canon_r(hd, V.WVal{}), acc}),
          aslot(V.JPair{x1, x2, x3})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd,
          V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JSpan{+x1, +x2}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
        V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad,
            root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JSpan{x1, x2},
        V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JSpan{x1, x2})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WArr{}), Parse.run(M4.tj_r(hd,
            V.WVal{}),
          Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1,
              x2},
          V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{rpush_r(V.JSpan{x1, x2}, V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JSpan{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
              V.WArr{}),
          zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
              Parse.P{bad,
          root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}, ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      hd_ok = M2.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WArr{}), h)
      tl_ok = M2.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WArr{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(hd, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2,
        x3,
        x4}, V.WArr{})), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.run(M4.tj_r(hd, V.WVal{}),
            Parse.P{bad,
          root,
        Parse.FArr{acc, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FArr{rpush_r(V.JBind{x1, x2, x3, x4},
        V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(M4.tj_r(hd, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.P{bad, root, Parse.FArr{acc,
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.run(M4.tj_r(hd,
          V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WArr{}), Parse.P{bad, root,
          Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk}), Parse.P{bad, root,
          Parse.FArr{rpush_r(V.JBind{x1, x2, x3, x4}, V.JCons{canon_r(hd, V.WVal{}), acc}), aslot(V.JBind{x1, x2, x3,
          x4})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4},
          V.WArr{}), zz), Parse.run(M4.tj_r(hd, V.WVal{}), Parse.P{bad, root, Parse.FArr{acc, Parse.SValue{}} <> stk}),
          Parse.P{bad, root, Parse.FArr{V.JCons{canon_r(hd, V.WVal{}), acc}, Parse.SComma{}} <> stk},
            ih_hd(hd_ok)({==})),
        ih_tl(tl_ok)))

# pv for an object cell, by what follows it
law pv_pair_r:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +h: {V.wf.go(V.JPair{kk, vv, rr}, V.WObj{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> pg_r(vv, V.WVal{}, bad, root, Parse.FObj{acc,
    Parse.KOwn{kk}, Parse.SValue{}} <> stk, V.JNil{})
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> pg_r(rr, V.WObj{}, bad, root, stk,
    V.JPair{kk, canon_r(vv, V.WVal{}), acc})
  pg_r(V.JPair{kk, vv, rr}, V.WObj{}, bad, root, stk, acc)

def pv_pair_r(rr, kk, vv, h, bad, root, stk, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      ih_v(v_ok)({==})
    case V.JNull{}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JNull{}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNull{})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}),
            Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNull{}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JNull{})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBool{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBool{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JBool{x1}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JBool{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JBool{x1}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JNum{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JNum{x1}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNum{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNum{x1}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JStr{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JStr{x1}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JStr{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JStr{x1}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JArr{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JArr{x1}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JArr{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JArr{x1}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JObj{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JObj{x1}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JObj{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JObj{x1}, V.JPair{kk,
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JCons{+x1, +x2}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad,
            root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JCons{x1, x2}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JCons{x1, x2})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
            V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv,
            V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JCons{x1, x2},
          V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JCons{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
              V.WObj{}),
          zz), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{kk, canon_r(vv,
          V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JPair{+x1, +x2, +x3}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2,
        x3},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad,
            root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JPair{x1, x2, x3}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}),
        Parse.KOwn{""}, oslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JPair{x1,
        x2, x3}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(M4.tj_r(vv,
          V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JPair{x1, x2, x3},
          V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JPair{x1, x2,
          x3})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3},
          V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc,
          Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JSpan{+x1, +x2}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad,
            root,
        Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})), Parse.P{bad, root,
        Parse.FObj{ppush_r(V.JSpan{x1, x2}, V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JSpan{x1, x2})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
            V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv,
            V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
          Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JSpan{x1, x2},
          V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JSpan{x1,
          x2})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
              V.WObj{}),
          zz), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{kk, canon_r(vv,
          V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2,
        x3,
        x4}, V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk},
        Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}),
            Parse.run(M4.tj_r(vv,
        V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk}, Parse.SValue{}} <> stk})),
        Parse.P{bad, root, Parse.FObj{ppush_r(V.JBind{x1, x2, x3, x4}, V.JPair{kk, canon_r(vv,
        V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc,
        Parse.KOwn{kk}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.run(M4.tj_r(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{kk},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad,
          root, Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JBind{x1, x2, x3, x4},
          V.JPair{kk, canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3,
          x4})} <> stk}, Equal.cong(Parse.P, Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4},
          V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc,
          Parse.KOwn{kk}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{kk, canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""},
          Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))

# pv for an object cell, by what follows it
law pv_bind_r:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +h: {V.wf.go(V.JBind{src, nn, vv, rr}, V.WObj{}) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> pg_r(vv, V.WVal{}, bad, root, Parse.FObj{acc,
    Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk, V.JNil{})
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> pg_r(rr, V.WObj{}, bad, root, stk,
    V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc})
  pg_r(V.JBind{src, nn, vv, rr}, V.WObj{}, bad, root, stk, acc)

def pv_bind_r(rr, src, nn, vv, h, bad, root, stk, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      ih_v(v_ok)({==})
    case V.JNull{}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNull{},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNull{})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}),
            Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNull{},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JNull{})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBool{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBool{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JBool{x1},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JBool{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JBool{x1},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JBool{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBool{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JNum{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNum{x1},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JNum{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JNum{x1},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JNum{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JNum{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JStr{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JStr{x1},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JStr{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JStr{x1},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JStr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JStr{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JArr{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JArr{x1},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JArr{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JArr{x1},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JArr{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JArr{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JObj{+x1}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{x1}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{x1},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JObj{x1},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JObj{x1})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}),
          Parse.P{bad,
        root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JObj{x1},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JObj{x1})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JObj{x1}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
              Parse.P{bad,
            root,
          Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JCons{+x1, +x2}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JCons{x1, x2},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JCons{x1, x2})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2},
            V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv,
            V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JCons{x1, x2},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JCons{x1, x2})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JCons{x1, x2}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
            Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JPair{+x1, +x2, +x3}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{x1, x2, x3}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2,
        x3},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JPair{x1, x2, x3},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JPair{x1, x2, x3})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2,
            x3},
        V.WObj{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Parse.run(M4.tj_r(vv,
          V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), Parse.P{bad,
              root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JPair{x1, x2, x3},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JPair{x1, x2, x3})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JPair{x1, x2, x3}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JSpan{+x1, +x2}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{x1, x2}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
        V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JSpan{x1, x2},
        V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""},
        oslot(V.JSpan{x1, x2})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2},
            V.WObj{}),
        Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
        Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), Parse.run(M4.tj_r(vv,
            V.WVal{}),
          Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(V.JSpan{x1, x2},
          V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
          Parse.KOwn{""}, oslot(V.JSpan{x1, x2})} <> stk}, Equal.cong(Parse.P, Parse.P,
          zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JSpan{x1, x2}, V.WObj{}), zz), Parse.run(M4.tj_r(vv, V.WVal{}),
            Parse.P{bad,
          root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))},
          Parse.SValue{}} <> stk}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn,
          U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))
    case V.JBind{+x1, +x2, +x3, +x4}:
      v_ok = M2.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      r_ok = M2.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{x1, x2, x3, x4}, V.WObj{}), h)
      Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
          Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2,
        x3,
        x4}, V.WObj{})), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
        U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4},
            V.WObj{}),
        Parse.run(M4.tj_r(vv, V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src,
        nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.P{bad, root, Parse.FObj{ppush_r(V.JBind{x1, x2, x3,
        x4}, V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}),
        Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, prun_app(M4.tj_r(vv, V.WVal{}),
        Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.P{bad, root, Parse.FObj{acc,
        Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))}, Parse.SValue{}} <> stk}),
        Equal.trans(Parse.P, Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), Parse.run(M4.tj_r(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
          U32.is_zero(nn))}, Parse.SValue{}} <> stk})), Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4},
          V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)),
          canon_r(vv, V.WVal{}), acc}, Parse.KOwn{""}, Parse.SComma{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{ppush_r(V.JBind{x1, x2, x3, x4}, V.JPair{V.span.str(src, nn, U32.is_zero(nn)),
          canon_r(vv, V.WVal{}), acc}), Parse.KOwn{""}, oslot(V.JBind{x1, x2, x3, x4})} <> stk}, Equal.cong(Parse.P,
          Parse.P, zz => Parse.run(Lex.TComma{} <> M4.tj_r(V.JBind{x1, x2, x3, x4}, V.WObj{}), zz),
              Parse.run(M4.tj_r(vv,
          V.WVal{}), Parse.P{bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
          U32.is_zero(nn))}, Parse.SValue{}} <> stk}), Parse.P{bad, root,
          Parse.FObj{V.JPair{V.span.str(src, nn, U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc},
          Parse.KOwn{""}, Parse.SComma{}} <> stk}, ih_v(v_ok)({==})),
        ih_r(r_ok)))

# the parser on a well-formed value's tokens
law pv_r:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +acc: V.Json
  pg_r(val, sh, bad, root, stk, acc)

def pv_r(val, sh, h, bad, root, stk, acc):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          _hr => {==}
        case V.WArr{}:
          M2.no(pg_r(V.JNull{}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JNull{}, V.WObj{}, bad, root, stk, acc), h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          pv_bool_r(bb, bad, root, stk)
        case V.WArr{}:
          M2.no(pg_r(V.JBool{bb}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JBool{bb}, V.WObj{}, bad, root, stk, acc), h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          _hr => step_num(raw, h, bad, root, stk)
        case V.WArr{}:
          M2.no(pg_r(V.JNum{raw}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JNum{raw}, V.WObj{}, bad, root, stk, acc), h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          hr => put_str_ready(stk, root, txt, bad, hr)
        case V.WArr{}:
          M2.no(pg_r(V.JStr{txt}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JStr{txt}, V.WObj{}, bad, root, stk, acc), h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          hr =>
            Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}]),
              Parse.step.open_arr(Parse.P{bad, root, stk})), Parse.run(List.append(&2, Lex.Tok, M4.tj_r(items,
                  V.WArr{}),
              [Lex.TCloseArr{}]), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}), Parse.put(stk,
              root, V.JArr{canon_r(items, V.WArr{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run(List.append(&2,
              Lex.Tok, M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}]), zz), Parse.step.open_arr(Parse.P{bad, root, stk}),
              Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}, open_arr_ready(bad, root, stk, hr)),
              Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}]),
                Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}), Parse.run([Lex.TCloseArr{}],
                Parse.run(M4.tj_r(items, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk})),
                Parse.put(stk, root, V.JArr{canon_r(items, V.WArr{})}, bad), prun_app(M4.tj_r(items, V.WArr{}),
                [Lex.TCloseArr{}], Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}),
              Equal.trans(Parse.P, Parse.run([Lex.TCloseArr{}], Parse.run(M4.tj_r(items, V.WArr{}), Parse.P{bad, root,
                Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk})), Parse.run([Lex.TCloseArr{}], Parse.P{bad, root,
                Parse.FArr{rpush_r(items, V.JNil{}), aslot(items)} <> stk}), Parse.put(stk, root, V.JArr{canon_r(items,
                V.WArr{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run([Lex.TCloseArr{}], zz),
                Parse.run(M4.tj_r(items, V.WArr{}), Parse.P{bad, root, Parse.FArr{V.JNil{}, Parse.SValue{}} <> stk}),
                Parse.P{bad, root, Parse.FArr{rpush_r(items, V.JNil{}), aslot(items)} <> stk}, pv_r(items, V.WArr{}, h,
                bad, root, stk, V.JNil{})),
              close_after_arr_r(items, bad, root, stk))))
        case V.WArr{}:
          M2.no(pg_r(V.JArr{items}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JArr{items}, V.WObj{}, bad, root, stk, acc), h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          hr =>
            Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              Parse.step.open_obj(Parse.P{bad, root, stk})), Parse.run(List.append(&2, Lex.Tok, M4.tj_r(pairs,
                  V.WObj{}),
              [Lex.TCloseObj{}]), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk}),
              Parse.put(stk, root, V.JObj{canon_r(pairs, V.WObj{})}, bad), Equal.cong(Parse.P, Parse.P,
              zz => Parse.run(List.append(&2, Lex.Tok, M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}]), zz),
              Parse.step.open_obj(Parse.P{bad, root, stk}), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
              Parse.SKey{}} <> stk}, open_obj_ready(bad, root, stk, hr)),
              Equal.trans(Parse.P, Parse.run(List.append(&2, Lex.Tok, M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}]),
                Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk}),
                Parse.run([Lex.TCloseObj{}], Parse.run(M4.tj_r(pairs, V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JNil{},
                Parse.KOwn{""}, Parse.SKey{}} <> stk})), Parse.put(stk, root, V.JObj{canon_r(pairs, V.WObj{})}, bad),
                prun_app(M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}], Parse.P{bad, root, Parse.FObj{V.JNil{},
                Parse.KOwn{""}, Parse.SKey{}} <> stk}),
              Equal.trans(Parse.P, Parse.run([Lex.TCloseObj{}], Parse.run(M4.tj_r(pairs, V.WObj{}), Parse.P{bad, root,
                Parse.FObj{V.JNil{}, Parse.KOwn{""}, Parse.SKey{}} <> stk})), Parse.run([Lex.TCloseObj{}], Parse.P{bad,
                root, Parse.FObj{ppush_r(pairs, V.JNil{}), Parse.KOwn{""}, oslot(pairs)} <> stk}), Parse.put(stk, root,
                V.JObj{canon_r(pairs, V.WObj{})}, bad), Equal.cong(Parse.P, Parse.P, zz => Parse.run([Lex.TCloseObj{}],
                zz), Parse.run(M4.tj_r(pairs, V.WObj{}), Parse.P{bad, root, Parse.FObj{V.JNil{}, Parse.KOwn{""},
                Parse.SKey{}} <> stk}), Parse.P{bad, root, Parse.FObj{ppush_r(pairs, V.JNil{}), Parse.KOwn{""},
                oslot(pairs)} <> stk}, pv_r(pairs, V.WObj{}, h, bad, root, stk, V.JNil{})),
              close_after_obj_r(pairs, bad, root, stk))))
        case V.WArr{}:
          M2.no(pg_r(V.JObj{pairs}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JObj{pairs}, V.WObj{}, bad, root, stk, acc), h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          M2.no(pg_r(V.JNil{}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          M2.no(pg_r(V.JCons{hd, tl}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          pv_cons_r(tl, hd, h, bad, root, stk, acc, xx => pv_r(hd, V.WVal{}, xx, bad, root, Parse.FArr{acc,
            Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv_r(tl, V.WArr{}, xx, bad, root, stk, V.JCons{canon_r(hd, V.WVal{}), acc}))
        case V.WObj{}:
          M2.no(pg_r(V.JCons{hd, tl}, V.WObj{}, bad, root, stk, acc), h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no(pg_r(V.JPair{kk, vv, rr}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          M2.no(pg_r(V.JPair{kk, vv, rr}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          pv_pair_r(rr, kk, vv, h, bad, root, stk, acc,
            xx => pv_r(vv, V.WVal{}, xx, bad, root, Parse.FObj{acc, Parse.KOwn{kk},
              Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv_r(rr, V.WObj{}, xx, bad, root, stk, V.JPair{kk, canon_r(vv, V.WVal{}), acc}))
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          hr => put_str_ready(stk, root, V.span.str(src, nn, U32.is_zero(nn)), bad, hr)
        case V.WArr{}:
          M2.no(pg_r(V.JSpan{src, nn}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          M2.no(pg_r(V.JSpan{src, nn}, V.WObj{}, bad, root, stk, acc), h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M2.no(pg_r(V.JBind{src, nn, vv, rr}, V.WVal{}, bad, root, stk, acc), h)
        case V.WArr{}:
          M2.no(pg_r(V.JBind{src, nn, vv, rr}, V.WArr{}, bad, root, stk, acc), h)
        case V.WObj{}:
          pv_bind_r(rr, src, nn, vv, h, bad, root, stk, acc,
            xx => pv_r(vv, V.WVal{}, xx, bad, root, Parse.FObj{acc, Parse.KOwn{V.span.str(src, nn,
              U32.is_zero(nn))}, Parse.SValue{}} <> stk, V.JNil{}),
            xx => pv_r(rr, V.WObj{}, xx, bad, root, stk, V.JPair{V.span.str(src, nn,
              U32.is_zero(nn)), canon_r(vv, V.WVal{}), acc}))

# WP-G: rows that follow from the round trip

# the value of a Some; null for None
def unsome(mb: Maybe<&2, V.Json>) -> V.Json:
  match mb:
    case None{}:
      V.JNull{}
    case Some{jj}:
      jj
