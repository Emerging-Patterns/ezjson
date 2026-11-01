# the parser state stays well-formed through closing brackets, braces and
# colons
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/BuiltValuesWellFormed.bend as L1
import ./LexemeOrder.bend as M1
import ./WellFormedCells.bend as M2

# laws/BuiltValuesWellFormed.bend, the parse half: parse's state only ever holds well-formed values

# a finished root is well-formed
def minv(root: Maybe<&2, V.Json>) -> Type:
  match root:
    case None{}:
      Unit
    case Some{jj}:
      {V.wf(jj) == True{} : Bool}

# an open frame's cells are well-formed
def frinv(fr: Parse.Frame) -> Type:
  match fr:
    case Parse.FArr{items, _}:
      {V.wf.go(items, V.WArr{}) == True{} : Bool}
    case Parse.FObj{pairs, _, _}:
      {V.wf.go(pairs, V.WObj{}) == True{} : Bool}

# every open frame's cells are well-formed
def finv(stk: List<&2, Parse.Frame>) -> Type:
  match stk:
    case Nil{}:
      Unit
    case fr <> rest:
      (frinv(fr) & finv(rest))

# the parser's state holds only well-formed values
def pinv(st: Parse.P) -> Type:
  match st:
    case Parse.P{_bad, root, stk}:
      (minv(root) & finv(stk))

# a string key's text is well-formed
law text_wf:
  for key: Parse.Key
  {V.wf(Parse.put.text(key)) == True{} : Bool}

def text_wf(key):
  match key:
    case Parse.KOwn{_txt}:
      {==}
    case Parse.KCut{_src, _nn}:
      {==}

# well-formed array cells reversed onto well-formed cells
law rev_wf_arr:
  for +cells: V.Json
  for +acc: V.Json
  for +hc: {V.wf.go(cells, V.WArr{}) == True{} : Bool}
  for ha: {V.wf.go(acc, V.WArr{}) == True{} : Bool}
  {V.wf.go(V.reverse(cells, acc), V.WArr{}) == True{} : Bool}

def rev_wf_arr(cells, acc, hc, ha):
  match cells:
    case V.JNull{}:
      M1.no({V.wf.go(V.reverse(V.JNull{}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JBool{+x1}:
      M1.no({V.wf.go(V.reverse(V.JBool{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JNum{+x1}:
      M1.no({V.wf.go(V.reverse(V.JNum{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JStr{+x1}:
      M1.no({V.wf.go(V.reverse(V.JStr{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JArr{+x1}:
      M1.no({V.wf.go(V.reverse(V.JArr{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JObj{+x1}:
      M1.no({V.wf.go(V.reverse(V.JObj{x1}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JNil{}:
      ha
    case V.JCons{+x1, +x2}:
      rev_wf_arr(x2, V.JCons{x1, acc}, M1.stop_r(V.wf(x1), V.wf.go(x2, V.WArr{}), hc),
        M2.cons_wf(x1, acc, M1.stop_l(V.wf(x1), V.wf.go(x2, V.WArr{}), hc), ha))
    case V.JPair{+x1, +x2, +x3}:
      M1.no({V.wf.go(V.reverse(V.JPair{x1, x2, x3}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JSpan{+x1, +x2}:
      M1.no({V.wf.go(V.reverse(V.JSpan{x1, x2}, acc), V.WArr{}) == True{} : Bool}, hc)
    case V.JBind{+x1, +x2, +x3, +x4}:
      M1.no({V.wf.go(V.reverse(V.JBind{x1, x2, x3, x4}, acc), V.WArr{}) == True{} : Bool}, hc)

# well-formed object cells reversed onto well-formed cells
law rev_wf_obj:
  for +cells: V.Json
  for +acc: V.Json
  for +hc: {V.wf.go(cells, V.WObj{}) == True{} : Bool}
  for ha: {V.wf.go(acc, V.WObj{}) == True{} : Bool}
  {V.wf.go(V.reverse(cells, acc), V.WObj{}) == True{} : Bool}

def rev_wf_obj(cells, acc, hc, ha):
  match cells:
    case V.JNull{}:
      M1.no({V.wf.go(V.reverse(V.JNull{}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JBool{+x1}:
      M1.no({V.wf.go(V.reverse(V.JBool{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JNum{+x1}:
      M1.no({V.wf.go(V.reverse(V.JNum{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JStr{+x1}:
      M1.no({V.wf.go(V.reverse(V.JStr{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JArr{+x1}:
      M1.no({V.wf.go(V.reverse(V.JArr{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JObj{+x1}:
      M1.no({V.wf.go(V.reverse(V.JObj{x1}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JNil{}:
      ha
    case V.JCons{+x1, +x2}:
      M1.no({V.wf.go(V.reverse(V.JCons{x1, x2}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JPair{+x1, +x2, +x3}:
      rev_wf_obj(x3, V.JPair{x1, x2, acc}, M1.stop_r(V.wf(x2), V.wf.go(x3, V.WObj{}), hc),
        M2.pair_wf(Parse.KOwn{x1}, x2, acc, M1.stop_l(V.wf(x2), V.wf.go(x3, V.WObj{}), hc), ha))
    case V.JSpan{+x1, +x2}:
      M1.no({V.wf.go(V.reverse(V.JSpan{x1, x2}, acc), V.WObj{}) == True{} : Bool}, hc)
    case V.JBind{+x1, +x2, +x3, +x4}:
      rev_wf_obj(x4, V.JBind{x1, x2, x3, acc}, M1.stop_r(V.wf(x3), V.wf.go(x4, V.WObj{}), hc),
        M2.pair_wf(Parse.KCut{x1, x2}, x3, acc, M1.stop_l(V.wf(x3), V.wf.go(x4, V.WObj{}), hc), ha))

# put keeps the state well-formed, given a well-formed value
law put_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  for +bad: Bool
  for hv: {V.wf(vv) == True{} : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.put(stk, root, vv, bad))

def put_inv(stk, root, vv, _bad, hv, h):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          (hv, Unit{})
        case Some{_rr}:
          (hr, _hs) = h
          (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, (hf, hrest)) = h
              (hr, (M2.cons_wf(vv, items, hv, hf), hrest))
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, (hf, hrest)) = h
              (hr, (M2.pair_wf(key, vv, pairs, hv, hf), hrest))
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})

# a colon keeps the state well-formed
law colon_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.colon(stk, root, bad))

def colon_inv(stk, _root, _bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              h

# a comma keeps the state well-formed
law comma_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.comma(stk, root, bad))

def comma_inv(stk, _root, _bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              h
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              h
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})

# a string keeps the state well-formed
law str_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +key: Parse.Key
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.put.str(stk, root, key, bad))

def str_inv(stk, root, key, bad, h):
  match stk:
    case Nil{}:
      put_inv([], root, Parse.put.text(key), bad, text_wf(key), h)
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              put_inv(Parse.FArr{items, Parse.SValue{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SComma{}:
              put_inv(Parse.FArr{items, Parse.SComma{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SKey{}:
              put_inv(Parse.FArr{items, Parse.SKey{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SColon{}:
              put_inv(Parse.FArr{items, Parse.SColon{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
        case Parse.FObj{+pairs, +k2, slot}:
          match slot:
            case Parse.SValue{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SComma{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)
            case Parse.SKey{}:
              h
            case Parse.SColon{}:
              put_inv(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest, root, Parse.put.text(key), bad, text_wf(key), h)

# close_arr_inv, for one frame
law ca_arr:
  for slot: Parse.Slot
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, Parse.FArr{items, slot} <> rest})
  pinv(Parse.close_arr(Parse.FArr{items, slot} <> rest, root, bad))

def ca_arr(slot, items, rest, root, bad, h):
  match slot:
    case Parse.SValue{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, (_hf, hrest)) = h
          put_inv(rest, root, V.JArr{V.JNil{}}, bad, {==}, (hr, hrest))
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SComma{}:
      (hr, (hf, hrest)) = h
      +it = items
      ec = Equal.sym(Parse.P, Parse.close_arr(Parse.FArr{it, Parse.SComma{}} <> rest, root, bad),
        Parse.put(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad), M1.close_arr_comma(it, rest, root, bad))
      %ec : pinv(_)
      put_inv(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad, rev_wf_arr(it, V.JNil{}, hf, {==}), (hr, hrest))
    case Parse.SKey{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SColon{}:
      match items:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})

# a closing bracket keeps the state well-formed
law close_arr_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.close_arr(stk, root, bad))

def close_arr_inv(stk, root, bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{items, slot}:
          ca_arr(slot, items, rest, root, bad, h)
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})

# close_obj_inv, for one frame
law co_obj:
  for slot: Parse.Slot
  for pairs: V.Json
  for +key: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, Parse.FObj{pairs, key, slot} <> rest})
  pinv(Parse.close_obj(Parse.FObj{pairs, key, slot} <> rest, root, bad))

def co_obj(slot, pairs, key, rest, root, bad, h):
  match slot:
    case Parse.SValue{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SComma{}:
      (hr, (hf, hrest)) = h
      +ps = pairs
      ec = Equal.sym(Parse.P, Parse.close_obj(Parse.FObj{ps, key, Parse.SComma{}} <> rest, root, bad),
        Parse.put(rest, root, V.JObj{V.reverse(ps, V.JNil{})}, bad), M1.close_obj_comma(ps, key, rest, root, bad))
      %ec : pinv(_)
      put_inv(rest, root, V.JObj{V.reverse(ps, V.JNil{})}, bad, rev_wf_obj(ps, V.JNil{}, hf, {==}), (hr, hrest))
    case Parse.SKey{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, (_hf, hrest)) = h
          put_inv(rest, root, V.JObj{V.JNil{}}, bad, {==}, (hr, hrest))
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})
    case Parse.SColon{}:
      match pairs:
        case V.JNull{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBool{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNum{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JStr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JArr{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JObj{+x1}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JNil{}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JCons{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JPair{+x1, +x2, +x3}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JSpan{+x1, +x2}:
          (hr, _rest) = h
          (hr, Unit{})
        case V.JBind{+x1, +x2, +x3, +x4}:
          (hr, _rest) = h
          (hr, Unit{})

# a closing brace keeps the state well-formed
law close_obj_inv:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.close_obj(stk, root, bad))

def close_obj_inv(stk, root, bad, h):
  match stk:
    case Nil{}:
      (hr, _rest) = h
      (hr, Unit{})
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, slot}:
          match slot:
            case Parse.SValue{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SComma{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SKey{}:
              (hr, _rest) = h
              (hr, Unit{})
            case Parse.SColon{}:
              (hr, _rest) = h
              (hr, Unit{})
        case Parse.FObj{pairs, +key, slot}:
          co_obj(slot, pairs, key, rest, root, bad, h)

# opening an array keeps the state well-formed
law oa_inv:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.open_arr.go(bad, root, stk, ok))

def oa_inv(ok, _bad, _root, _stk, h):
  match ok:
    case True{}:
      (hr, hs) = h
      (hr, ({==}, hs))
    case False{}:
      (hr, _hs) = h
      (hr, Unit{})

# opening an object keeps the state well-formed
law oo_inv:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.open_obj.go(bad, root, stk, ok))

def oo_inv(ok, _bad, _root, _stk, h):
  match ok:
    case True{}:
      (hr, hs) = h
      (hr, ({==}, hs))
    case False{}:
      (hr, _hs) = h
      (hr, Unit{})

# a word parse accepts is a well-formed value
law word_wf:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for eo: {Bool.or(b1, Bool.or(b2, Bool.or(b3, V.num.ok(raw)))) == True{} : Bool}
  {V.wf(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{raw})))) == True{} : Bool}

def word_wf(b1, b2, b3, _raw, eo):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              eo

# a word keeps the state well-formed
law sw_inv:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for eo: {Parse.word.ok(raw) == ok : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.word.go(raw, Parse.P{bad, root, stk}, ok))

def sw_inv(ok, raw, bad, root, stk, eo, h):
  match ok:
    case True{}:
      put_inv(stk, root, Parse.word(raw), bad, word_wf(String.eq(raw, "null"), String.eq(raw, "true"),
        String.eq(raw, "false"), raw, eo), h)
    case False{}:
      h

# a number span keeps the state well-formed
law sk_inv:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for eo: {V.num.ok(raw) == ok : Bool}
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.ok(raw, ok)))

def sk_inv(ok, raw, bad, root, stk, eo, h):
  match ok:
    case True{}:
      put_inv(stk, root, V.JNum{raw}, bad, eo, h)
    case False{}:
      h

# a word span keeps the state well-formed
law sg_inv:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for +src: String
  for +nn: U32
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for h: pinv(Parse.P{bad, root, stk})
  pinv(Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, aa, bb, cc)))

def sg_inv(aa, bb, cc, src, nn, bad, root, stk, h):
  match aa:
    case True{}:
      put_inv(stk, root, V.JNull{}, bad, {==}, h)
    case False{}:
      match bb:
        case True{}:
          put_inv(stk, root, V.JBool{True{}}, bad, {==}, h)
        case False{}:
          match cc:
            case True{}:
              put_inv(stk, root, V.JBool{False{}}, bad, {==}, h)
            case False{}:
              +raw = V.span.str(src, nn, U32.is_zero(nn))
              sk_inv(V.num.ok(raw), raw, bad, root, stk, {==}, h)

# one token keeps the state well-formed
law step_inv:
  for tok: Lex.Tok
  for st: Parse.P
  for h: pinv(st)
  pinv(Parse.step(tok, st))

def step_inv(tok, st, h):
  match tok:
    case Lex.TOpenArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          oa_inv(Parse.step.ready(stk, root), bad, root, stk, h)
    case Lex.TOpenObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          oo_inv(Parse.step.ready(stk, root), bad, root, stk, h)
    case Lex.TCloseArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_arr_inv(stk, root, bad, h)
    case Lex.TCloseObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_obj_inv(stk, root, bad, h)
    case Lex.TColon{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          colon_inv(stk, root, bad, h)
    case Lex.TComma{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          comma_inv(stk, root, bad, h)
    case Lex.TStr{+txt}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_inv(stk, root, Parse.KOwn{txt}, bad, h)
    case Lex.TWord{+raw}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          sw_inv(Parse.word.ok(raw), raw, bad, root, stk, {==}, h)
    case Lex.TStrS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_inv(stk, root, Parse.KCut{src, nn}, bad, h)
    case Lex.TWordS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          sg_inv(V.span.eq(src, nn, "null"), V.span.eq(src, nn, "true"), V.span.eq(src, nn, "false"), src, nn, bad,
            root, stk, h)
    case Lex.TBad{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          h

# every token keeps the state well-formed
law run_inv:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for h: pinv(st)
  pinv(Parse.run(xs, st))

def run_inv(xs, st, h):
  match xs:
    case Nil{}:
      h
    case +tok <> rest:
      run_inv(rest, Parse.step(tok, st), step_inv(tok, st, h))

# a finished parse of a well-formed state is well-formed
law fin_wf:
  for bad: Bool
  for stk: List<&2, Parse.Frame>
  for root: Maybe<&2, V.Json>
  for h: (minv(root) & finv(stk))
  {L1.wf_m(Parse.result(bad, stk, root)) == True{} : Bool}

def fin_wf(bad, stk, root, h):
  match bad:
    case True{}:
      {==}
    case False{}:
      match stk:
        case +_fr <> +_rest:
          {==}
        case Nil{}:
          match root:
            case None{}:
              {==}
            case Some{_jj}:
              (hr, _hs) = h
              hr

# a finished parse is well-formed
law fin_inv:
  for st: Parse.P
  for h: pinv(st)
  {L1.wf_m(Parse.finish(st)) == True{} : Bool}

def fin_inv(st, h):
  match st:
    case Parse.P{bad, root, stk}:
      fin_wf(bad, stk, root, h)

def L1.parse_wf(txt):
  fin_inv(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}),
    run_inv(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}, (Unit{}, Unit{})))
