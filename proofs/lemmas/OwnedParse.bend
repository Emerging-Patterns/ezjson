# the parser on owned values: brackets, braces and colons
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./LexemeOrder.bend as M3
import ./WellFormedCells.bend as M4

# a key with its span read out
def ownk(key: Parse.Key) -> Parse.Key:
  match key:
    case Parse.KOwn{txt}:
      Parse.KOwn{txt}
    case Parse.KCut{src, +nn}:
      Parse.KOwn{V.span.str(src, nn, U32.is_zero(nn))}

# an open frame with its spans read out
def ownf(fr: Parse.Frame) -> Parse.Frame:
  match fr:
    case Parse.FArr{items, slot}:
      Parse.FArr{D1.own(items), slot}
    case Parse.FObj{pairs, key, slot}:
      Parse.FObj{D1.own(pairs), ownk(key), slot}

# the open frames with their spans read out
def owns(stk: List<&2, Parse.Frame>) -> List<&2, Parse.Frame>:
  match stk:
    case Nil{}:
      Nil{}
    case fr <> rest:
      ownf(fr) <> owns(rest)

# the parser's state with its spans read out
def ownp(st: Parse.P) -> Parse.P:
  match st:
    case Parse.P{bad, root, stk}:
      Parse.P{bad, D1.own_m(root), owns(stk)}

# whether a value may go next does not look at spans
law ready_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {Parse.step.ready(owns(stk), D1.own_m(root)) == Parse.step.ready(stk, root) : Bool}

def ready_own(stk, root):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          {==}
        case Some{_jj}:
          {==}
    case fr <> _rest:
      match fr:
        case Parse.FArr{_items, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}
        case Parse.FObj{_pairs, _key, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}

# a pair put under a key, owned
law pair_own:
  for key: Parse.Key
  for +vv: V.Json
  for +pairs: V.Json
  {D1.own(Parse.put.pair(key, vv, pairs)) == Parse.put.pair(ownk(key), D1.own(vv), D1.own(pairs)) : V.Json}

def pair_own(key, _vv, _pairs):
  match key:
    case Parse.KOwn{_txt}:
      {==}
    case Parse.KCut{_src, _nn}:
      {==}

# a string key's value, owned
law text_own:
  for key: Parse.Key
  {D1.own(Parse.put.text(key)) == Parse.put.text(ownk(key)) : V.Json}

def text_own(key):
  match key:
    case Parse.KOwn{_txt}:
      {==}
    case Parse.KCut{_src, _nn}:
      {==}

# put, owned, is put of the owned value on the owned state
law put_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  for +bad: Bool
  {ownp(Parse.put(stk, root, vv, bad)) == Parse.put(owns(stk), D1.own_m(root), D1.own(vv), bad) : Parse.P}

def put_own(stk, root, vv, bad):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          {==}
        case Some{_rr}:
          {==}
    case fr <> +rest:
      match fr:
        case Parse.FArr{_items, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}
        case Parse.FObj{+pairs, +key, slot}:
          match slot:
            case Parse.SValue{}:
              Equal.cong(V.Json, Parse.P, zz => Parse.P{bad, D1.own_m(root), Parse.FObj{zz, Parse.KOwn{""},
                Parse.SComma{}} <> owns(rest)},
                D1.own(Parse.put.pair(key, vv, pairs)), Parse.put.pair(ownk(key), D1.own(vv), D1.own(pairs)),
                pair_own(key, vv, pairs))
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}

# reversing cells, owned
law own_rev:
  for +cells: V.Json
  for +acc: V.Json
  {D1.own(V.reverse(cells, acc)) == V.reverse(D1.own(cells), D1.own(acc)) : V.Json}

def own_rev(cells, acc):
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
      own_rev(x2, V.JCons{x1, acc})
    case V.JPair{+x1, +x2, +x3}:
      own_rev(x3, V.JPair{x1, x2, acc})
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      own_rev(x4, V.JBind{x1, x2, x3, acc})

# a closing bracket on an array frame, owned
law ca_own:
  for slot: Parse.Slot
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.close_arr(Parse.FArr{items, slot} <> rest, root, bad)) ==
    Parse.close_arr(owns(Parse.FArr{items, slot} <> rest), D1.own_m(root), bad) : Parse.P}

def ca_own(slot, items, rest, root, bad):
  match slot:
    case Parse.SValue{}:
      match items:
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
          put_own(rest, root, V.JArr{V.JNil{}}, bad)
        case V.JCons{+x1, +x2}:
          {==}
        case V.JPair{+x1, +x2, +x3}:
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}
    case Parse.SComma{}:
      +it = items
      Equal.trans(Parse.P, ownp(Parse.close_arr(Parse.FArr{it, Parse.SComma{}} <> rest, root, bad)),
        ownp(Parse.put(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad)), Parse.close_arr(Parse.FArr{D1.own(it),
        Parse.SComma{}} <> owns(rest), D1.own_m(root), bad), Equal.cong(Parse.P, Parse.P, zz => ownp(zz),
        Parse.close_arr(Parse.FArr{it, Parse.SComma{}} <> rest, root, bad), Parse.put(rest, root, V.JArr{V.reverse(it,
        V.JNil{})}, bad),
        M3.close_arr_comma(it, rest, root, bad)),
        Equal.trans(Parse.P, ownp(Parse.put(rest, root, V.JArr{V.reverse(it, V.JNil{})}, bad)), Parse.put(owns(rest),
          D1.own_m(root), V.JArr{D1.own(V.reverse(it, V.JNil{}))}, bad), Parse.close_arr(Parse.FArr{D1.own(it),
          Parse.SComma{}} <> owns(rest), D1.own_m(root), bad), put_own(rest, root, V.JArr{V.reverse(it, V.JNil{})},
          bad),
        Equal.trans(Parse.P, Parse.put(owns(rest), D1.own_m(root), V.JArr{D1.own(V.reverse(it, V.JNil{}))}, bad),
          Parse.put(owns(rest), D1.own_m(root), V.JArr{V.reverse(D1.own(it), V.JNil{})}, bad),
          Parse.close_arr(Parse.FArr{D1.own(it), Parse.SComma{}} <> owns(rest), D1.own_m(root), bad),
          Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(rest), D1.own_m(root), V.JArr{zz}, bad),
          D1.own(V.reverse(it, V.JNil{})),
        V.reverse(D1.own(it), V.JNil{}), own_rev(it, V.JNil{})),
        Equal.sym(Parse.P, Parse.close_arr(Parse.FArr{D1.own(it), Parse.SComma{}} <> owns(rest), D1.own_m(root),
          bad), Parse.put(owns(rest), D1.own_m(root), V.JArr{V.reverse(D1.own(it), V.JNil{})}, bad),
          M3.close_arr_comma(D1.own(it), owns(rest), D1.own_m(root), bad)))))
    case Parse.SKey{}:
      match items:
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
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}
    case Parse.SColon{}:
      match items:
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
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}

# a closing brace on an object frame, owned
law co_own:
  for slot: Parse.Slot
  for pairs: V.Json
  for +key: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.close_obj(Parse.FObj{pairs, key, slot} <> rest, root, bad)) ==
    Parse.close_obj(owns(Parse.FObj{pairs, key, slot} <> rest), D1.own_m(root), bad) : Parse.P}

def co_own(slot, pairs, key, rest, root, bad):
  match slot:
    case Parse.SKey{}:
      match pairs:
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
          put_own(rest, root, V.JObj{V.JNil{}}, bad)
        case V.JCons{+x1, +x2}:
          {==}
        case V.JPair{+x1, +x2, +x3}:
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}
    case Parse.SComma{}:
      +it = pairs
      Equal.trans(Parse.P, ownp(Parse.close_obj(Parse.FObj{it, key, Parse.SComma{}} <> rest, root, bad)),
        ownp(Parse.put(rest, root, V.JObj{V.reverse(it, V.JNil{})}, bad)), Parse.close_obj(Parse.FObj{D1.own(it),
        ownk(key), Parse.SComma{}} <> owns(rest), D1.own_m(root), bad), Equal.cong(Parse.P, Parse.P, zz => ownp(zz),
        Parse.close_obj(Parse.FObj{it, key, Parse.SComma{}} <> rest, root, bad), Parse.put(rest, root,
        V.JObj{V.reverse(it, V.JNil{})}, bad),
        M3.close_obj_comma(it, key, rest, root, bad)),
        Equal.trans(Parse.P, ownp(Parse.put(rest, root, V.JObj{V.reverse(it, V.JNil{})}, bad)), Parse.put(owns(rest),
          D1.own_m(root), V.JObj{D1.own(V.reverse(it, V.JNil{}))}, bad), Parse.close_obj(Parse.FObj{D1.own(it),
          ownk(key), Parse.SComma{}} <> owns(rest), D1.own_m(root), bad), put_own(rest, root, V.JObj{V.reverse(it,
          V.JNil{})}, bad),
        Equal.trans(Parse.P, Parse.put(owns(rest), D1.own_m(root), V.JObj{D1.own(V.reverse(it, V.JNil{}))}, bad),
          Parse.put(owns(rest), D1.own_m(root), V.JObj{V.reverse(D1.own(it), V.JNil{})}, bad),
          Parse.close_obj(Parse.FObj{D1.own(it), ownk(key), Parse.SComma{}} <> owns(rest), D1.own_m(root), bad),
          Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(rest), D1.own_m(root), V.JObj{zz}, bad),
          D1.own(V.reverse(it, V.JNil{})),
        V.reverse(D1.own(it), V.JNil{}), own_rev(it, V.JNil{})),
        Equal.sym(Parse.P, Parse.close_obj(Parse.FObj{D1.own(it), ownk(key), Parse.SComma{}} <> owns(rest),
          D1.own_m(root), bad), Parse.put(owns(rest), D1.own_m(root), V.JObj{V.reverse(D1.own(it), V.JNil{})},
          bad), M3.close_obj_comma(D1.own(it), ownk(key), owns(rest), D1.own_m(root), bad)))))
    case Parse.SValue{}:
      match pairs:
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
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}
    case Parse.SColon{}:
      match pairs:
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
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}

# a closing bracket, owned
law close_arr_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.close_arr(stk, root, bad)) == Parse.close_arr(owns(stk), D1.own_m(root), bad) : Parse.P}

def close_arr_own(stk, root, bad):
  match stk:
    case Nil{}:
      {==}
    case fr <> +rest:
      match fr:
        case Parse.FArr{items, slot}:
          ca_own(slot, items, rest, root, bad)
        case Parse.FObj{_pairs, _key, _slot}:
          {==}

# a closing brace, owned
law close_obj_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.close_obj(stk, root, bad)) == Parse.close_obj(owns(stk), D1.own_m(root), bad) : Parse.P}

def close_obj_own(stk, root, bad):
  match stk:
    case Nil{}:
      {==}
    case fr <> +rest:
      match fr:
        case Parse.FArr{_items, _slot}:
          {==}
        case Parse.FObj{pairs, +key, slot}:
          co_own(slot, pairs, key, rest, root, bad)

# a colon, owned
law colon_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.step.colon(stk, root, bad)) == Parse.step.colon(owns(stk), D1.own_m(root), bad) : Parse.P}

def colon_own(stk, _root, _bad):
  match stk:
    case Nil{}:
      {==}
    case fr <> _rest:
      match fr:
        case Parse.FArr{_items, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}
        case Parse.FObj{_pairs, _key, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}

# a comma, owned
law comma_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {ownp(Parse.step.comma(stk, root, bad)) == Parse.step.comma(owns(stk), D1.own_m(root), bad) : Parse.P}

def comma_own(stk, _root, _bad):
  match stk:
    case Nil{}:
      {==}
    case fr <> _rest:
      match fr:
        case Parse.FArr{_items, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}
        case Parse.FObj{_pairs, _key, slot}:
          match slot:
            case Parse.SValue{}:
              {==}
            case Parse.SComma{}:
              {==}
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              {==}

# a string, owned
law str_own:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +key: Parse.Key
  for +bad: Bool
  {ownp(Parse.put.str(stk, root, key, bad)) == Parse.put.str(owns(stk), D1.own_m(root), ownk(key), bad) : Parse.P}

def str_own(stk, root, key, bad):
  match stk:
    case Nil{}:
      Equal.trans(Parse.P, ownp(Parse.put([], root, Parse.put.text(key), bad)),
        Parse.put(owns([]), D1.own_m(root), D1.own(Parse.put.text(key)), bad),
        Parse.put(owns([]), D1.own_m(root), Parse.put.text(ownk(key)), bad),
        put_own([], root, Parse.put.text(key), bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(owns([]), D1.own_m(root), zz, bad), D1.own(Parse.put.text(key)),
          Parse.put.text(ownk(key)), text_own(key)))
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, +slot}:
          Equal.trans(Parse.P, ownp(Parse.put(Parse.FArr{items, slot} <> rest, root, Parse.put.text(key), bad)),
            Parse.put(owns(Parse.FArr{items, slot} <> rest), D1.own_m(root), D1.own(Parse.put.text(key)), bad),
            Parse.put(owns(Parse.FArr{items, slot} <> rest), D1.own_m(root), Parse.put.text(ownk(key)), bad),
            put_own(Parse.FArr{items, slot} <> rest, root, Parse.put.text(key), bad),
            Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(Parse.FArr{items, slot} <> rest), D1.own_m(root), zz,
              bad), D1.own(Parse.put.text(key)),
              Parse.put.text(ownk(key)), text_own(key)))
        case Parse.FObj{+pairs, +k2, slot}:
          match slot:
            case Parse.SKey{}:
              {==}
            case Parse.SValue{}:
              Equal.trans(Parse.P, ownp(Parse.put(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest, root,
                Parse.put.text(key), bad)),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest), D1.own_m(root),
                  D1.own(Parse.put.text(key)), bad),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest), D1.own_m(root),
                  Parse.put.text(ownk(key)), bad),
                put_own(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest, root, Parse.put.text(key), bad),
                Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest),
                  D1.own_m(root), zz, bad), D1.own(Parse.put.text(key)),
                  Parse.put.text(ownk(key)), text_own(key)))
            case Parse.SComma{}:
              Equal.trans(Parse.P, ownp(Parse.put(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest, root,
                Parse.put.text(key), bad)),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest), D1.own_m(root),
                  D1.own(Parse.put.text(key)), bad),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest), D1.own_m(root),
                  Parse.put.text(ownk(key)), bad),
                put_own(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest, root, Parse.put.text(key), bad),
                Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest),
                  D1.own_m(root), zz, bad), D1.own(Parse.put.text(key)),
                  Parse.put.text(ownk(key)), text_own(key)))
            case Parse.SColon{}:
              Equal.trans(Parse.P, ownp(Parse.put(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest, root,
                Parse.put.text(key), bad)),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest), D1.own_m(root),
                  D1.own(Parse.put.text(key)), bad),
                Parse.put(owns(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest), D1.own_m(root),
                  Parse.put.text(ownk(key)), bad),
                put_own(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest, root, Parse.put.text(key), bad),
                Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest),
                  D1.own_m(root), zz, bad), D1.own(Parse.put.text(key)),
                  Parse.put.text(ownk(key)), text_own(key)))

# a word's value, with the literal tests named, holds no span
law word_own.go:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  {D1.own(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{raw})))) == Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}},
    Bool.pick(V.Json, b3, V.JBool{False{}}, V.JNum{raw}))) : V.Json}

def word_own.go(b1, b2, b3, _raw):
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
              {==}

# a word, on the state with spans read out
law sw_own:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {ownp(Parse.step.word.go(raw, Parse.P{bad, root, stk}, ok)) == Parse.step.word.go(raw, Parse.P{bad, D1.own_m(root),
    owns(stk)}, ok) : Parse.P}

def sw_own(ok, raw, bad, root, stk):
  match ok:
    case True{}:
      Equal.trans(Parse.P, ownp(Parse.put(stk, root, Parse.word(raw), bad)),
        Parse.put(owns(stk), D1.own_m(root), D1.own(Parse.word(raw)), bad),
        Parse.put(owns(stk), D1.own_m(root), Parse.word(raw), bad),
        put_own(stk, root, Parse.word(raw), bad),
        Equal.cong(V.Json, Parse.P, zz => Parse.put(owns(stk), D1.own_m(root), zz, bad), D1.own(Parse.word(raw)),
          Parse.word(raw), word_own.go(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw)))
    case False{}:
      {==}

# the literal a word is, by its tests
law word_is:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for e1: {String.eq(raw, "null") == b1 : Bool}
  for e2: {String.eq(raw, "true") == b2 : Bool}
  for e3: {String.eq(raw, "false") == b3 : Bool}
  {Parse.word(raw) == Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{raw}))) : V.Json}

def word_is(_b1, b2, b3, raw, e1, e2, e3):
  %e1 : {Parse.word(raw) == Bool.pick(V.Json, _, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json,
    b3, V.JBool{False{}}, V.JNum{raw}))) : V.Json}
  %e2 : {Parse.word(raw) == Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{}, Bool.pick(V.Json, _, V.JBool{True{}},
    Bool.pick(V.Json, b3, V.JBool{False{}}, V.JNum{raw}))) : V.Json}
  %e3 : {Parse.word(raw) == Bool.pick(V.Json, String.eq(raw, "null"), V.JNull{}, Bool.pick(V.Json, String.eq(raw,
    "true"), V.JBool{True{}}, Bool.pick(V.Json, _, V.JBool{False{}}, V.JNum{raw}))) : V.Json}
  {==}

# a number span's check, against the word's
law sk_word:
  for ok: Bool
  for +raw: String
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for ew: {Parse.word(raw) == V.JNum{raw} : V.Json}
  {Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.ok(raw, ok)) == Parse.step.word.go(raw, Parse.P{bad,
    root, stk}, ok) : Parse.P}

def sk_word(ok, raw, bad, root, stk, ew):
  match ok:
    case True{}:
      Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, zz, bad), V.JNum{raw}, Parse.word(raw),
        Equal.sym(V.Json, Parse.word(raw), V.JNum{raw}, ew))
    case False{}:
      {==}

# a word span against its word, with the literal tests named
law span_word.go:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +src: String
  for +nn: U32
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  for +e1: {String.eq(V.span.str(src, nn, U32.is_zero(nn)), "null") == b1 : Bool}
  for +e2: {String.eq(V.span.str(src, nn, U32.is_zero(nn)), "true") == b2 : Bool}
  for +e3: {String.eq(V.span.str(src, nn, U32.is_zero(nn)), "false") == b3 : Bool}
  {Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, b1, b2, b3)) ==
    Parse.step.word.go(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root, stk}, Bool.or(b1, Bool.or(b2,
      Bool.or(b3, V.num.ok(V.span.str(src, nn, U32.is_zero(nn))))))) : Parse.P}

def span_word.go(b1, b2, b3, src, nn, bad, root, stk, e1, e2, e3):
  match b1:
    case True{}:
      Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, zz, bad), V.JNull{}, Parse.word(V.span.str(src, nn,
        U32.is_zero(nn))),
        Equal.sym(V.Json, Parse.word(V.span.str(src, nn, U32.is_zero(nn))), V.JNull{}, word_is(True{}, b2, b3,
          V.span.str(src, nn, U32.is_zero(nn)), e1, e2, e3)))
    case False{}:
      match b2:
        case True{}:
          Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, zz, bad), V.JBool{True{}}, Parse.word(V.span.str(src,
            nn, U32.is_zero(nn))),
            Equal.sym(V.Json, Parse.word(V.span.str(src, nn, U32.is_zero(nn))), V.JBool{True{}}, word_is(False{},
              True{}, b3, V.span.str(src, nn, U32.is_zero(nn)), e1, e2, e3)))
        case False{}:
          match b3:
            case True{}:
              Equal.cong(V.Json, Parse.P, zz => Parse.put(stk, root, zz, bad), V.JBool{False{}},
                Parse.word(V.span.str(src, nn, U32.is_zero(nn))),
                Equal.sym(V.Json, Parse.word(V.span.str(src, nn, U32.is_zero(nn))), V.JBool{False{}}, word_is(False{},
                  False{}, True{}, V.span.str(src, nn, U32.is_zero(nn)), e1, e2, e3)))
            case False{}:
              sk_word(V.num.ok(V.span.str(src, nn, U32.is_zero(nn))), V.span.str(src, nn, U32.is_zero(nn)), bad, root,
                stk,
                word_is(False{}, False{}, False{}, V.span.str(src, nn, U32.is_zero(nn)), e1, e2, e3))

# a word span acts as the word it covers
law span_word:
  for +src: String
  for +nn: U32
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {Parse.step.span(src, nn, Parse.P{bad, root, stk}) == Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)),
    Parse.P{bad, root, stk}) : Parse.P}

def span_word(src, nn, bad, root, stk):
  +zz = U32.is_zero(nn)
  s1 = Equal.sym(Bool, V.span.eq(src, nn, "null"), String.eq(V.span.str(src, nn, U32.is_zero(nn)), "null"),
    M1.span_eq_go(src, zz, "null", nn))
  s2 = Equal.sym(Bool, V.span.eq(src, nn, "true"), String.eq(V.span.str(src, nn, U32.is_zero(nn)), "true"),
    M1.span_eq_go(src, zz, "true", nn))
  s3 = Equal.sym(Bool, V.span.eq(src, nn, "false"), String.eq(V.span.str(src, nn, U32.is_zero(nn)), "false"),
    M1.span_eq_go(src, zz, "false", nn))
  %s1 : {Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, _, V.span.eq(src, nn, "true"),
    V.span.eq(src, nn, "false"))) == Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root,
      stk}) : Parse.P}
  %s2 : {Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, String.eq(V.span.str(src, nn,
    U32.is_zero(nn)), "null"), _,
    V.span.eq(src, nn, "false"))) == Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root,
      stk}) : Parse.P}
  %s3 : {Parse.step.span.open(Parse.P{bad, root, stk}, Parse.step.span.go(src, nn, String.eq(V.span.str(src, nn,
    U32.is_zero(nn)), "null"), String.eq(V.span.str(src, nn, U32.is_zero(nn)), "true"),
    _)) == Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root, stk}) : Parse.P}
  span_word.go(String.eq(V.span.str(src, nn, U32.is_zero(nn)), "null"), String.eq(V.span.str(src, nn, U32.is_zero(nn)),
    "true"), String.eq(V.span.str(src, nn, U32.is_zero(nn)), "false"), src, nn, bad, root, stk, {==}, {==}, {==})

# opening an array, owned
law oa_own:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {ownp(Parse.step.open_arr.go(bad, root, stk, ok)) == Parse.step.open_arr.go(bad, D1.own_m(root), owns(stk),
    ok) : Parse.P}

def oa_own(ok, _bad, _root, _stk):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# opening an object, owned
law oo_own:
  for ok: Bool
  for +bad: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {ownp(Parse.step.open_obj.go(bad, root, stk, ok)) == Parse.step.open_obj.go(bad, D1.own_m(root), owns(stk),
    ok) : Parse.P}

def oo_own(ok, _bad, _root, _stk):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# one token, owned: the state with spans read out steps as the token with its
# span read out
law step_own:
  for tok: Lex.Tok
  for st: Parse.P
  {ownp(Parse.step(tok, st)) == Parse.step(M3.den(tok), ownp(st)) : Parse.P}

def step_own(tok, st):
  match tok:
    case Lex.TOpenArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          Equal.trans(Parse.P, ownp(Parse.step.open_arr.go(bad, root, stk, Parse.step.ready(stk, root))),
            Parse.step.open_arr.go(bad, D1.own_m(root), owns(stk), Parse.step.ready(stk, root)),
            Parse.step.open_arr.go(bad, D1.own_m(root), owns(stk), Parse.step.ready(owns(stk), D1.own_m(root))),
            oa_own(Parse.step.ready(stk, root), bad, root, stk),
            Equal.cong(Bool, Parse.P, zz => Parse.step.open_arr.go(bad, D1.own_m(root), owns(stk), zz),
              Parse.step.ready(stk, root),
              Parse.step.ready(owns(stk), D1.own_m(root)), Equal.sym(Bool, Parse.step.ready(owns(stk),
                D1.own_m(root)),
                Parse.step.ready(stk, root), ready_own(stk, root))))
    case Lex.TOpenObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          Equal.trans(Parse.P, ownp(Parse.step.open_obj.go(bad, root, stk, Parse.step.ready(stk, root))),
            Parse.step.open_obj.go(bad, D1.own_m(root), owns(stk), Parse.step.ready(stk, root)),
            Parse.step.open_obj.go(bad, D1.own_m(root), owns(stk), Parse.step.ready(owns(stk), D1.own_m(root))),
            oo_own(Parse.step.ready(stk, root), bad, root, stk),
            Equal.cong(Bool, Parse.P, zz => Parse.step.open_obj.go(bad, D1.own_m(root), owns(stk), zz),
              Parse.step.ready(stk, root),
              Parse.step.ready(owns(stk), D1.own_m(root)), Equal.sym(Bool, Parse.step.ready(owns(stk),
                D1.own_m(root)),
                Parse.step.ready(stk, root), ready_own(stk, root))))
    case Lex.TCloseArr{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_arr_own(stk, root, bad)
    case Lex.TCloseObj{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          close_obj_own(stk, root, bad)
    case Lex.TColon{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          colon_own(stk, root, bad)
    case Lex.TComma{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          comma_own(stk, root, bad)
    case Lex.TStr{+txt}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_own(stk, root, Parse.KOwn{txt}, bad)
    case Lex.TWord{+raw}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          sw_own(Parse.word.ok(raw), raw, bad, root, stk)
    case Lex.TStrS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          str_own(stk, root, Parse.KCut{src, nn}, bad)
    case Lex.TWordS{+src, +nn}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          Equal.trans(Parse.P, ownp(Parse.step.span(src, nn, Parse.P{bad, root, stk})),
            ownp(Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root, stk})),
            Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, D1.own_m(root), owns(stk)}),
            Equal.cong(Parse.P, Parse.P, zz => ownp(zz), Parse.step.span(src, nn, Parse.P{bad, root, stk}),
              Parse.step.word(V.span.str(src, nn, U32.is_zero(nn)), Parse.P{bad, root, stk}), span_word(src, nn, bad,
                root, stk)),
            sw_own(Parse.word.ok(V.span.str(src, nn, U32.is_zero(nn))), V.span.str(src, nn, U32.is_zero(nn)), bad,
              root, stk))
    case Lex.TBad{}:
      match st:
        case Parse.P{+bad, +root, +stk}:
          {==}

# the parser, owned, is the parser on tokens with their spans read out
law run_own:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  {ownp(Parse.run(xs, st)) == Parse.run(M3.dens(xs), ownp(st)) : Parse.P}

def run_own(xs, st):
  match xs:
    case Nil{}:
      {==}
    case +tok <> +rest:
      Equal.trans(Parse.P, ownp(Parse.run(rest, Parse.step(tok, st))), Parse.run(M3.dens(rest), ownp(Parse.step(tok,
          st))),
        Parse.run(M3.dens(rest), Parse.step(M3.den(tok), ownp(st))), run_own(rest, Parse.step(tok, st)),
        Equal.cong(Parse.P, Parse.P, zz => Parse.run(M3.dens(rest), zz), ownp(Parse.step(tok, st)),
          Parse.step(M3.den(tok), ownp(st)), step_own(tok, st)))

# a finished parse, owned
law fin_own.go:
  for bad: Bool
  for stk: List<&2, Parse.Frame>
  for root: Maybe<&2, V.Json>
  {D1.own_m(Parse.result(bad, stk, root)) == Parse.result(bad, owns(stk), D1.own_m(root)) : Maybe<&2, V.Json>}

def fin_own.go(bad, stk, root):
  match bad:
    case True{}:
      {==}
    case False{}:
      match stk:
        case _fr <> _rest:
          {==}
        case Nil{}:
          match root:
            case None{}:
              {==}
            case Some{_jj}:
              {==}

# a finished parse, owned, is the owned state finished
law fin_own:
  for st: Parse.P
  {D1.own_m(Parse.finish(st)) == Parse.finish(ownp(st)) : Maybe<&2, V.Json>}

def fin_own(st):
  match st:
    case Parse.P{bad, root, stk}:
      fin_own.go(bad, stk, root)

# whether a Maybe is None
def is_none(mb: Maybe<&2, V.Json>) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{_jj}:
      False{}

# laws/ByteOrderMarkRefused.bend: a byte order mark

# appending lists is associative
law lapp_assoc:
  for +kk: List<&2, Lex.Tok>
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, kk, aa), bb) == List.append(&2, Lex.Tok, kk, List.append(&2,
    Lex.Tok, aa, bb)) : List<&2, Lex.Tok>}

def lapp_assoc(kk, aa, bb):
  match kk:
    case Nil{}:
      {==}
    case hd <> +tl:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => hd <> zz, List.append(&2, Lex.Tok, List.append(&2,
        Lex.Tok, tl, aa), bb), List.append(&2, Lex.Tok, tl, List.append(&2, Lex.Tok, aa, bb)), lapp_assoc(tl, aa, bb))

# tokens added below, twice, are added once
law lex_app2:
  for lx: Lex.Lex
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  {M2.lex.app(M2.lex.app(lx, aa), bb) == M2.lex.app(lx, List.append(&2, Lex.Tok, aa, bb)) : Lex.Lex}

def lex_app2(lx, aa, bb):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      Equal.cong(List<&2, Lex.Tok>, Lex.Lex, zz => Lex.Lex{md, bf, zz}, List.append(&2, Lex.Tok, List.append(&2,
        Lex.Tok, tk, aa), bb), List.append(&2, Lex.Tok, tk, List.append(&2, Lex.Tok, aa, bb)),
        lapp_assoc(tk, aa, bb))

# feeding a character does not look at the tokens below
law feed_app:
  for +ch: Char
  for lx: Lex.Lex
  for +tt: List<&2, Lex.Tok>
  {Lex.feed(ch, M2.lex.app(lx, tt)) == M2.lex.app(Lex.feed(ch, lx), tt) : Lex.Lex}

def feed_app(ch, lx, tt):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      +f0 = Lex.feed(ch, Lex.Lex{md, bf, []})
      Equal.trans(Lex.Lex, Lex.feed(ch, Lex.Lex{md, bf, List.append(&2, Lex.Tok, tk, tt)}), M2.lex.app(f0,
          List.append(&2,
        Lex.Tok, tk, tt)),
        M2.lex.app(Lex.feed(ch, Lex.Lex{md, bf, tk}), tt), M2.pass.feed(ch, md, bf, List.append(&2, Lex.Tok, tk, tt)),
        Equal.sym(Lex.Lex, M2.lex.app(Lex.feed(ch, Lex.Lex{md, bf, tk}), tt), M2.lex.app(f0, List.append(&2, Lex.Tok,
            tk,
          tt)),
          Equal.trans(Lex.Lex, M2.lex.app(Lex.feed(ch, Lex.Lex{md, bf, tk}), tt), M2.lex.app(M2.lex.app(f0, tk), tt),
            M2.lex.app(f0, List.append(&2, Lex.Tok, tk, tt)),
            Equal.cong(Lex.Lex, Lex.Lex, zz => M2.lex.app(zz, tt), Lex.feed(ch, Lex.Lex{md, bf, tk}), M2.lex.app(f0,
                tk),
              M2.pass.feed(ch, md, bf, tk)),
            lex_app2(f0, tk, tt))))

# running the character lexer does not look at the tokens below
law run_pass:
  for +cs: List<&2, Char>
  for +lx: Lex.Lex
  for +tt: List<&2, Lex.Tok>
  {Lex.run(cs, M2.lex.app(lx, tt)) == M2.lex.app(Lex.run(cs, lx), tt) : Lex.Lex}

def run_pass(cs, lx, tt):
  match cs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(hd, M2.lex.app(lx, tt))), Lex.run(tl, M2.lex.app(Lex.feed(hd, lx), tt)),
        M2.lex.app(Lex.run(tl, Lex.feed(hd, lx)), tt),
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(tl, zz), Lex.feed(hd, M2.lex.app(lx, tt)), M2.lex.app(Lex.feed(hd,
            lx),
          tt),
          feed_app(hd, lx, tt)),
        run_pass(tl, Lex.feed(hd, lx), tt))

# laws/ParsesExactlyJsonTexts.bend: the tokens of a text parse accepts are its value's

# the token a key stands for
def ktok(key: Parse.Key) -> Lex.Tok:
  match key:
    case Parse.KOwn{txt}:
      Lex.TStr{txt}
    case Parse.KCut{src, +nn}:
      Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))}

# a comma on top when cells came before
def sepr(cells: V.Json, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match cells:
    case V.JNil{}:
      acc
    case _:
      Lex.TComma{} <> acc

# the tokens an open frame has read, reversed onto acc
def frrev(fr: Parse.Frame, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match fr:
    case Parse.FArr{items, Parse.SComma{}}:
      List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(items, V.JNil{}), V.WArr{}), Lex.TOpenArr{} <> acc)
    case Parse.FArr{+items, _}:
      sepr(items, List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(items, V.JNil{}), V.WArr{}), Lex.TOpenArr{} <> acc))
    case Parse.FObj{pairs, _, Parse.SComma{}}:
      List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(pairs, V.JNil{}), V.WObj{}), Lex.TOpenObj{} <> acc)
    case Parse.FObj{+pairs, _, Parse.SKey{}}:
      sepr(pairs, List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(pairs, V.JNil{}), V.WObj{}), Lex.TOpenObj{} <> acc))
    case Parse.FObj{+pairs, key, Parse.SColon{}}:
      ktok(key) <> sepr(pairs, List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(pairs, V.JNil{}), V.WObj{}),
        Lex.TOpenObj{} <> acc))
    case Parse.FObj{+pairs, key, Parse.SValue{}}:
      Lex.TColon{} <> ktok(key) <> sepr(pairs, List.reverse.go(&2, Lex.Tok, M4.tj_r(V.reverse(pairs, V.JNil{}),
          V.WObj{}),
        Lex.TOpenObj{} <> acc))

# the tokens the open frames have read, outermost first, reversed onto acc
def srev(stk: List<&2, Parse.Frame>, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match stk:
    case Nil{}:
      acc
    case fr <> rest:
      frrev(fr, srev(rest, acc))

# the tokens a finished root has read, reversed
def rrev(root: Maybe<&2, V.Json>) -> List<&2, Lex.Tok>:
  match root:
    case None{}:
      []
    case Some{rr}:
      List.reverse.go(&2, Lex.Tok, M4.tj_r(rr, V.WVal{}), [])

# the tokens a parser state has read, reversed
def rs(root: Maybe<&2, V.Json>, stk: List<&2, Parse.Frame>) -> List<&2, Lex.Tok>:
  srev(stk, rrev(root))

# unicode.sur, by its four comparisons
def sb(b1: Bool, b2: Bool, b3: Bool, b4: Bool) -> Lex.Sur:
  match b1 b2:
    case True{} True{}:
      Lex.SHi{}
    case _ _:
      Lex.unicode.sur.lo(b3, b4)
