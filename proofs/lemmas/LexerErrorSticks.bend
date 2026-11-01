# once the character lexer rejects a text, the error stays
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./LexemeOrder.bend as M1
import ./OwnedParse.bend as M2

# the character lexer, once it has rejected a text, stays rejected
law bad_run:
  for +cs: List<&2, Char>
  {Lex.run(cs, Lex.Lex{Lex.Bad{}, [], []}) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex}

def bad_run(cs):
  match cs:
    case Nil{}:
      {==}
    case _hd <> +tl:
      bad_run(tl)

# the parser's error flag
def pbad(st: Parse.P) -> Bool:
  match st:
    case Parse.P{bad, _root, _stk}:
      bad

# put keeps a raised error flag
law put_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  {pbad(Parse.put(stk, root, vv, True{})) == True{} : Bool}

def put_bad(stk, root, _vv):
  match stk:
    case Nil{}:
      match root:
        case None{}:
          {==}
        case Some{_rr}:
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

# a closing bracket keeps a raised error flag, for one frame
law cab:
  for slot: Parse.Slot
  for items: V.Json
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.close_arr(Parse.FArr{items, slot} <> rest, root, True{})) == True{} : Bool}

def cab(slot, items, rest, root):
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
          put_bad(rest, root, V.JArr{V.JNil{}})
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
      ec = Equal.sym(Parse.P, Parse.close_arr(Parse.FArr{it, Parse.SComma{}} <> rest, root, True{}),
        Parse.put(rest, root, V.JArr{V.reverse(it, V.JNil{})}, True{}), M1.close_arr_comma(it, rest, root, True{}))
      %ec : {pbad(_) == True{} : Bool}
      put_bad(rest, root, V.JArr{V.reverse(it, V.JNil{})})
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

# a closing brace keeps a raised error flag, for one frame
law cob:
  for slot: Parse.Slot
  for pairs: V.Json
  for +key: Parse.Key
  for +rest: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.close_obj(Parse.FObj{pairs, key, slot} <> rest, root, True{})) == True{} : Bool}

def cob(slot, pairs, key, rest, root):
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
          put_bad(rest, root, V.JObj{V.JNil{}})
        case V.JCons{+x1, +x2}:
          {==}
        case V.JPair{+x1, +x2, +x3}:
          {==}
        case V.JSpan{+x1, +x2}:
          {==}
        case V.JBind{+x1, +x2, +x3, +x4}:
          {==}
    case Parse.SComma{}:
      +ps = pairs
      ec = Equal.sym(Parse.P, Parse.close_obj(Parse.FObj{ps, key, Parse.SComma{}} <> rest, root, True{}),
        Parse.put(rest, root, V.JObj{V.reverse(ps, V.JNil{})}, True{}), M1.close_obj_comma(ps, key, rest, root, True{}))
      %ec : {pbad(_) == True{} : Bool}
      put_bad(rest, root, V.JObj{V.reverse(ps, V.JNil{})})
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

# a closing bracket keeps a raised error flag
law ca_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.close_arr(stk, root, True{})) == True{} : Bool}

def ca_bad(stk, root):
  match stk:
    case Nil{}:
      {==}
    case fr <> +rest:
      match fr:
        case Parse.FArr{items, slot}:
          cab(slot, items, rest, root)
        case Parse.FObj{_pairs, _key, _slot}:
          {==}

# a closing brace keeps a raised error flag
law co_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.close_obj(stk, root, True{})) == True{} : Bool}

def co_bad(stk, root):
  match stk:
    case Nil{}:
      {==}
    case fr <> +rest:
      match fr:
        case Parse.FArr{_items, _slot}:
          {==}
        case Parse.FObj{pairs, +key, slot}:
          cob(slot, pairs, key, rest, root)

# a colon keeps a raised error flag
law colon_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.step.colon(stk, root, True{})) == True{} : Bool}

def colon_bad(stk, _root):
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

# a comma keeps a raised error flag
law comma_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  {pbad(Parse.step.comma(stk, root, True{})) == True{} : Bool}

def comma_bad(stk, _root):
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

# a string keeps a raised error flag
law str_bad:
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +key: Parse.Key
  {pbad(Parse.put.str(stk, root, key, True{})) == True{} : Bool}

def str_bad(stk, root, key):
  match stk:
    case Nil{}:
      put_bad([], root, Parse.put.text(key))
    case fr <> +rest:
      match fr:
        case Parse.FArr{+items, +slot}:
          put_bad(Parse.FArr{items, slot} <> rest, root, Parse.put.text(key))
        case Parse.FObj{+pairs, +k2, slot}:
          match slot:
            case Parse.SValue{}:
              put_bad(Parse.FObj{pairs, k2, Parse.SValue{}} <> rest, root, Parse.put.text(key))
            case Parse.SComma{}:
              put_bad(Parse.FObj{pairs, k2, Parse.SComma{}} <> rest, root, Parse.put.text(key))
            case Parse.SKey{}:
              {==}
            case Parse.SColon{}:
              put_bad(Parse.FObj{pairs, k2, Parse.SColon{}} <> rest, root, Parse.put.text(key))

# opening an array keeps a raised error flag
law oa_bad:
  for ok: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {pbad(Parse.step.open_arr.go(True{}, root, stk, ok)) == True{} : Bool}

def oa_bad(ok, _root, _stk):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# opening an object keeps a raised error flag
law oo_bad:
  for ok: Bool
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {pbad(Parse.step.open_obj.go(True{}, root, stk, ok)) == True{} : Bool}

def oo_bad(ok, _root, _stk):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# a word keeps a raised error flag
law sw_bad:
  for ok: Bool
  for +raw: String
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {pbad(Parse.step.word.go(raw, Parse.P{True{}, root, stk}, ok)) == True{} : Bool}

def sw_bad(ok, raw, root, stk):
  match ok:
    case True{}:
      put_bad(stk, root, Parse.word(raw))
    case False{}:
      {==}

# a number span keeps a raised error flag
law sk_bad:
  for ok: Bool
  for +raw: String
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {pbad(Parse.step.span.open(Parse.P{True{}, root, stk}, Parse.step.span.ok(raw, ok))) == True{} : Bool}

def sk_bad(ok, raw, root, stk):
  match ok:
    case True{}:
      put_bad(stk, root, V.JNum{raw})
    case False{}:
      {==}

# a word span keeps a raised error flag
law sg_bad:
  for aa: Bool
  for bb: Bool
  for cc: Bool
  for +src: String
  for +nn: U32
  for +root: Maybe<&2, V.Json>
  for +stk: List<&2, Parse.Frame>
  {pbad(Parse.step.span.open(Parse.P{True{}, root, stk}, Parse.step.span.go(src, nn, aa, bb, cc))) == True{} : Bool}

def sg_bad(aa, bb, cc, src, nn, root, stk):
  match aa:
    case True{}:
      put_bad(stk, root, V.JNull{})
    case False{}:
      match bb:
        case True{}:
          put_bad(stk, root, V.JBool{True{}})
        case False{}:
          match cc:
            case True{}:
              put_bad(stk, root, V.JBool{False{}})
            case False{}:
              sk_bad(V.num.ok(V.span.str(src, nn, U32.is_zero(nn))), V.span.str(src, nn, U32.is_zero(nn)), root, stk)

# one token keeps a raised error flag
law step_bad:
  for tok: Lex.Tok
  for st: Parse.P
  for h: {pbad(st) == True{} : Bool}
  {pbad(Parse.step(tok, st)) == True{} : Bool}

def step_bad(tok, st, h):
  match tok:
    case Lex.TOpenArr{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TOpenArr{}, Parse.P{_, root, stk})) == True{} : Bool}
          oa_bad(Parse.step.ready(stk, root), root, stk)
    case Lex.TOpenObj{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TOpenObj{}, Parse.P{_, root, stk})) == True{} : Bool}
          oo_bad(Parse.step.ready(stk, root), root, stk)
    case Lex.TCloseArr{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TCloseArr{}, Parse.P{_, root, stk})) == True{} : Bool}
          ca_bad(stk, root)
    case Lex.TCloseObj{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TCloseObj{}, Parse.P{_, root, stk})) == True{} : Bool}
          co_bad(stk, root)
    case Lex.TColon{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TColon{}, Parse.P{_, root, stk})) == True{} : Bool}
          colon_bad(stk, root)
    case Lex.TComma{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TComma{}, Parse.P{_, root, stk})) == True{} : Bool}
          comma_bad(stk, root)
    case Lex.TStr{+txt}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TStr{txt}, Parse.P{_, root, stk})) == True{} : Bool}
          str_bad(stk, root, Parse.KOwn{txt})
    case Lex.TWord{+raw}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TWord{raw}, Parse.P{_, root, stk})) == True{} : Bool}
          sw_bad(Parse.word.ok(raw), raw, root, stk)
    case Lex.TStrS{+src, +nn}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TStrS{src, nn}, Parse.P{_, root, stk})) == True{} : Bool}
          str_bad(stk, root, Parse.KCut{src, nn})
    case Lex.TWordS{+src, +nn}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TWordS{src, nn}, Parse.P{_, root, stk})) == True{} : Bool}
          sg_bad(V.span.eq(src, nn, "null"), V.span.eq(src, nn, "true"), V.span.eq(src, nn, "false"), src, nn, root,
            stk)
    case Lex.TBad{}:
      match st:
        case Parse.P{bad, +root, +stk}:
          hs = Equal.sym(Bool, bad, True{}, h)
          %hs : {pbad(Parse.step(Lex.TBad{}, Parse.P{_, root, stk})) == True{} : Bool}
          {==}

# every token keeps a raised error flag
law run_bad:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for h: {pbad(st) == True{} : Bool}
  {pbad(Parse.run(xs, st)) == True{} : Bool}

def run_bad(xs, st, h):
  match xs:
    case Nil{}:
      h
    case +tok <> rest:
      run_bad(rest, Parse.step(tok, st), step_bad(tok, st, h))

# a state with its error flag raised finishes as None
law fin_bad:
  for st: Parse.P
  for h: {pbad(st) == True{} : Bool}
  {Parse.finish(st) == None{} : Maybe<&2, V.Json>}

def fin_bad(st, h):
  match st:
    case Parse.P{bad, +root, +stk}:
      hs = Equal.sym(Bool, bad, True{}, h)
      %hs : {Parse.result(_, stk, root) == None{} : Maybe<&2, V.Json>}
      {==}

# a parse result whose owned form is None is None
law own_m_none:
  for +mb: Maybe<&2, V.Json>
  for e: {D1.own_m(mb) == None{} : Maybe<&2, V.Json>}
  {mb == None{} : Maybe<&2, V.Json>}

def own_m_none(mb, e):
  match mb:
    case None{}:
      {==}
    case Some{+jj}:
      Empty.absurd({Some{jj} == None{} : Maybe<&2, V.Json>}, M1.false_true(Equal.cong(Maybe<&2, V.Json>, Bool,
        zz => M2.is_none(zz), Some{D1.own(jj)},
        None{}, e)))
